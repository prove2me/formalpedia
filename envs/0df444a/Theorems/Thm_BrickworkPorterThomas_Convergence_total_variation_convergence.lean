-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_total_variation_convergence
-- name    : BrickworkPorterThomas.Convergence.total_variation_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:17:16.235275+00:00
-- url     : https://prove2.me/theorems/16a878a6-3add-4482-934b-e90f3a564359
-- title:
--   Theorem 1.1 — brickwork output law converges to the Haar (Porter–Thomas) law in total variation
-- statement:
--   Let $n\ge2$ be even, $d=2^n$, and fix a bitstring $b\in\{0,1\}^n$. Let $P$ be the law of $p_U(b)=|\langle b|U|0^n\rangle|^2$ for $U\sim\mathcal C(l)$, the depth-$l$ brickwork Haar random circuit ensemble, and let $Q$ be its law for $U$ Haar random on $\mathrm{SU}(d)$ (the exact Porter–Thomas law, with density $(d-1)(1-p)^{d-2}$).
--
--   1. There is an absolute constant $C>0$ such that, whenever $\mathcal C(l)$ is a $d^{-k}$-approximate $k$-design with $k\ge2$,
--
--   $$
--   d_{TV}(P,Q)\le C\sqrt{\frac{\log k}{k}} .
--   $$
--
--   2. For every real $m\ge0$: if $k=\Theta(n^{2m}\log n)$ (with the design hypothesis of item 1), then $d_{TV}(P,Q)=O(n^{-m})$.
--   3. For every real $m\ge0$, the design order $k=\Theta(n^{2m}\log n)$ is achieved in depth $l=\Theta(n^{2m+1}\log n)$. That is, there are integers $k(n)\ge2$ and $l(n)$ with $k(n)=\Theta(n^{2m}\log n)$ and $l(n)=\Theta(n^{2m+1}\log n)$ such that $\mathcal C(l(n))$ is a $d^{-k(n)}$-approximate $k(n)$-design and
--
--   $$
--   d_{TV}(P,Q)\le\frac{C'}{n^{m}}\quad\text{for every } b .
--   $$
--
--   Polynomial-depth local random circuits therefore have output statistics inverse-polynomially close to Porter–Thomas, which is the statistical premise of linear cross-entropy benchmarking in random circuit sampling.
--
--   **Formalization Note** $Q$ is the exact Haar law, not the exponential approximation $de^{-dp}$. The constant in item 1 is chosen before $n,l,k,b$. The constants in items 2 and 3 depend only on $m$ and the stated $\Theta$-witnesses, and all bounds hold for every even $n\ge2$.
--
--   Differences from the source:
--
--   - encoding: n even, qubits 1..n on a ring, d = 2^n → n = 2M with M ≥ 1, qubits Fin (2M) (0-based), d = 2^(2M); reason: Definition 2.4 assumes n even; every even n ≥ 2 is some 2M; relabelling only
--   - encoding: layers numbered 1..l, odd layers on (1,2),(3,4),…, even layers on (2,3),…,(n,1) → layers numbered 0..l−1 with the pairs of the reused brickPair (Lean layer j is the source layer j+1); reason: index shift only; the pairs and the chronological order are the source’s
--   - encoding: a law ν on SU(d) (Definition 2.3) → a law on d×d complex matrices supported on SU(d) (Borel σ-algebra of the matrix space); reason: the twirl and the output probability only depend on the pushed-forward law; same instances
--   - encoding: diamond norm of M_ν^(k) − M_μH^(k) on the k-fold system → the reused stabilized trace-norm diamond norm, after relabelling the basis of the k-fold system (k-tuples of bitstrings) by Fin(d^k); reason: a basis relabelling is a unitary permutation and changes no trace norm
--   - encoding: d_TV(P,Q) ≤ O(√(log(k)/k)) → ∃ C > 0 before n, l, k, b with d_TV(P,Q) ≤ C √(log k / k); reason: the uniform constant of the O-notation
--   - encoding: if k = Θ(n^{2m} log n) then d_TV(P,Q) ≤ O(1/n^m) → ∀ real m ≥ 0, ∀ c₁ > 0, c₂: ∃ C′ > 0 with d_TV ≤ C′ n^{−m} for all even n ≥ 2 and all k ≥ 2 with c₁ n^{2m} log n ≤ k ≤ c₂ n^{2m} log n (and the design hypothesis); reason: O and Θ with explicit witnesses; since d_TV ≤ 1 a bound for large n and one for all n ≥ 2 differ only in the constant
--   - reading: “k = Θ(n^{2m} log n), which implies l = Θ(n^{2m+1} log n) by Theorem 2.5” → ∀ real m ≥ 0: ∃ integer sequences k(n) ≥ 2, l(n) with k(n) = Θ(n^{2m} log n), l(n) = Θ(n^{2m+1} log n) for every even n ≥ 2, C(l(n)) a d^{−k(n)}-approximate k(n)-design, and d_TV ≤ C′ n^{−m} for every b; reason: the depth claim made explicit as attainability of the design order in that depth; the Θ bounds are asserted for every even n ≥ 2, the stronger of the two readings
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §1, p. 2, Theorem 1.1, Eqs. (1)–(3); restated as Theorem 3.1, p. 8, Eqs. (27)–(29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Circuit
import Definitions.Def_FoundationsRL_DECLower_tvDist

namespace BrickworkPorterThomas.Convergence

open MeasureTheory

/-- Theorem 1.1 (p. 2; restated as Theorem 3.1, p. 8). On `n = 2M` qubits (`M ≥ 1`), `d = 2^n`,
let `P` be the law of `p_U(b) = |⟨b|U|0^n⟩|²` for `U ∼ C(l)` and `Q` its law for Haar `U ∈ SU(d)`.

1. There is one absolute constant `C > 0` such that whenever `C(l)` is a `d^{-k}`-approximate
   `k`-design with `k ≥ 2`, `d_TV(P, Q) ≤ C √(log k / k)`, for every `n`, `l`, `k`, `b`.
2. For every real `m ≥ 0` and Θ-witnesses `0 < c₁`, `c₂`: if `c₁ n^{2m} log n ≤ k ≤ c₂ n^{2m} log n`
   (and the design hypothesis), then `d_TV(P, Q) ≤ C' n^{-m}` with `C'` depending only on
   `m, c₁, c₂`.
3. For every real `m ≥ 0` there are design orders `k(n) = Θ(n^{2m} log n)` and depths
   `l(n) = Θ(n^{2m+1} log n)` (uniform Θ-constants, valid for every even `n ≥ 2`) such that
   `C(l(n))` is a `d^{-k(n)}`-approximate `k(n)`-design and `d_TV(P, Q) ≤ C' n^{-m}` for all `b`. -/
theorem total_variation_convergence :
    (∃ C : ℝ, 0 < C ∧ ∀ (M l k : ℕ) (b : Bits (2 * M)), 1 ≤ M → 2 ≤ k →
        IsApproxDesign (circuitLaw M l) k (designTol M k) →
        FoundationsRL.DECLower.tvDist (outputLaw M l b) (haarOutputLaw (2 * M) b) ≤
          C * Real.sqrt (Real.log k / k)) ∧
    (∀ m : ℝ, 0 ≤ m → ∀ c₁ c₂ : ℝ, 0 < c₁ → ∃ C : ℝ, 0 < C ∧
        ∀ (M l k : ℕ) (b : Bits (2 * M)), 1 ≤ M → 2 ≤ k →
        c₁ * ((2 * M : ℕ) : ℝ) ^ (2 * m) * Real.log (2 * M : ℕ) ≤ k →
        (k : ℝ) ≤ c₂ * ((2 * M : ℕ) : ℝ) ^ (2 * m) * Real.log (2 * M : ℕ) →
        IsApproxDesign (circuitLaw M l) k (designTol M k) →
        FoundationsRL.DECLower.tvDist (outputLaw M l b) (haarOutputLaw (2 * M) b) ≤
          C * ((2 * M : ℕ) : ℝ) ^ (-m)) ∧
    (∀ m : ℝ, 0 ≤ m → ∃ (kSeq lSeq : ℕ → ℕ) (a₁ a₂ e₁ e₂ C : ℝ),
        0 < a₁ ∧ 0 < a₂ ∧ 0 < e₁ ∧ 0 < e₂ ∧ 0 < C ∧
        ∀ M : ℕ, 1 ≤ M →
          2 ≤ kSeq (2 * M) ∧
          a₁ * ((2 * M : ℕ) : ℝ) ^ (2 * m) * Real.log (2 * M : ℕ) ≤ kSeq (2 * M) ∧
          (kSeq (2 * M) : ℝ) ≤ a₂ * ((2 * M : ℕ) : ℝ) ^ (2 * m) * Real.log (2 * M : ℕ) ∧
          e₁ * ((2 * M : ℕ) : ℝ) ^ (2 * m + 1) * Real.log (2 * M : ℕ) ≤ lSeq (2 * M) ∧
          (lSeq (2 * M) : ℝ) ≤ e₂ * ((2 * M : ℕ) : ℝ) ^ (2 * m + 1) * Real.log (2 * M : ℕ) ∧
          IsApproxDesign (circuitLaw M (lSeq (2 * M))) (kSeq (2 * M)) (designTol M (kSeq (2 * M))) ∧
          ∀ b : Bits (2 * M),
            FoundationsRL.DECLower.tvDist (outputLaw M (lSeq (2 * M)) b)
                (haarOutputLaw (2 * M) b) ≤ C * ((2 * M : ℕ) : ℝ) ^ (-m)) := by sorry

end BrickworkPorterThomas.Convergence
