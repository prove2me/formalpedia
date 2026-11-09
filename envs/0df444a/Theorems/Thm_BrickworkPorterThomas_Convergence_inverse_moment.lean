-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_inverse_moment
-- name    : BrickworkPorterThomas.Convergence.inverse_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:16:14.205187+00:00
-- url     : https://prove2.me/theorems/ffb00b2e-4585-4d5a-a225-d92a29bd9f3e
-- title:
--   Theorem 6.1 — inverse moment bound $E[R^{-1}]\le Kd$ for the mass entering a final gate
-- statement:
--   There are absolute constants $A,K>0$, with $K=1+11A$, such that the following holds. Let $U\sim\mathcal C(l)$ be a brickwork random circuit on $n$ qubits ($n$ even, $d=2^n$, depth at least one) whose law is a $d^{-k}$-approximate $k$-design with $k\ge8$. Factor $U=G_*C$, where $G_*$ is a fixed gate in the final layer with output pair $S_*$. For a fixed string $x$ on the complement of $S_*$, let
--
--   $$
--   R=\sum_{z\in\{0,1\}^{S_*}}|\langle z,x|C|0^n\rangle|^2 .
--   $$
--
--   Then
--
--   $$
--   \Pr[R\le t/d]\le A t^{12/11}\quad(0<t\le1),\qquad \mathbb E[R^{-1}]\le K\,d .
--   $$
--
--   This is a small-ball anticoncentration estimate for the probability mass entering one final gate, and, through Lemma 5.2, it gives the smoothness bound $\|f'\|_{L^1}=O(d)$ of the circuit's output density.
--
--   **Formalization Note** $K$ is uniform in $n,k,l$, the gate and the string. $E[R^{-1}]$ is a $[0,\infty]$-valued integral with $R^{-1}=+\infty$ at $R=0$, so almost-sure positivity of $R$ is part of the conclusion.
--
--   Differences from the source:
--
--   - encoding: n even, qubits 1..n on a ring, d = 2^n → n = 2M with M ≥ 1, qubits Fin (2M) (0-based), d = 2^(2M); reason: Definition 2.4 assumes n even; every even n ≥ 2 is some 2M; relabelling only
--   - encoding: U ∼ C(l) with a final layer → U ∼ C(l+1), final layer index l (0-based); reason: the final gate exists only for depth ≥ 1; every depth ≥ 1 is l+1
--   - encoding: a law ν on SU(d) (Definition 2.3) → a law on d×d complex matrices supported on SU(d) (Borel σ-algebra of the matrix space); reason: the twirl and the output probability only depend on the pushed-forward law; same instances
--   - encoding: diamond norm of M_ν^(k) − M_μH^(k) on the k-fold system → the reused stabilized trace-norm diamond norm, after relabelling the basis of the k-fold system (k-tuples of bitstrings) by Fin(d^k); reason: a basis relabelling is a unitary permutation and changes no trace norm
--   - encoding: x a fixed string on the complement of S_i → x a full bitstring whose entries on S_i are ignored; reason: every complementary string arises and only its entries off S_i enter R_i
--   - encoding: E[R^{-1}] as a real expectation → the [0,∞]-valued integral of (R)^{-1} with 1/0 = +∞; reason: finiteness is part of the conclusion, not presupposed
--   - encoding: E[R^{-1}] ≤ K d; the proof establishes Pr[R ≤ t/d] ≤ A t^{12/11} in Eq. (116) and K = 1 + 11 A in Eq. (154) → one pair of absolute constants A,K satisfying K = 1 + 11 A, with both the small-ball and inverse-moment conclusions; reason: keeps the explicit exponent and coefficient from the proof in the same item as the numbered result
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §6, p. 16, Theorem 6.1, Eqs. (115)–(116), (154), pp. 16–21, Eqs. (114)–(115); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Circuit

namespace BrickworkPorterThomas.Convergence

open MeasureTheory

/-- Theorem 6.1 (p. 16). There is a constant `K > 0` (independent of `n`, `k`, `l`, the gate and
the string) such that: if `U ∼ C(l+1)` on `n = 2M` qubits is a `d^{-k}`-approximate `k`-design
with `k ≥ 8`, `U = G_* C` with `G_*` a gate of the final layer with output pair `S_*`, and `x` is
a fixed string on the complement of `S_*`, then `R = Σ_{z ∈ {0,1}^{S_*}} |⟨z, x|C|0^n⟩|²`
satisfies `Pr[R ≤ t/d] ≤ A t^{12/11}` for `0 < t ≤ 1` (Eq. (116)) and
`E[R^{-1}] ≤ K d`, with `K = 1 + 11 A` (Eq. (154)).
The constants are uniform; `R^{-1} = +∞` where `R = 0`. -/
theorem inverse_moment : ∃ A K : ℝ, 0 < A ∧ 0 < K ∧ K = 1 + 11 * A ∧
    ∀ (M l k : ℕ) (p : Fin M) (x : Bits (2 * M)), 1 ≤ M → 8 ≤ k →
      IsApproxDesign (circuitLaw M (l + 1)) k (designTol M k) →
      (∀ t : ℝ, 0 < t → t ≤ 1 →
        gateLaw M (l + 1) {g | finalGateMass p x g ≤ t / (2 : ℝ) ^ (2 * M)} ≤
          ENNReal.ofReal (A * t ^ (12 / 11 : ℝ))) ∧
      ∫⁻ g, (ENNReal.ofReal (finalGateMass p x g))⁻¹ ∂gateLaw M (l + 1) ≤
        ENNReal.ofReal (K * (2 : ℝ) ^ (2 * M)) := by sorry

end BrickworkPorterThomas.Convergence
