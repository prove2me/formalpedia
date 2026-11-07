-- Prove2me | Theorems.Thm_AC02Frege_theorem_1_4_depth35_lower_bound
-- name    : AC02Frege.theorem_1_4_depth35_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:19.701081+00:00
-- url     : https://prove2.me/theorems/2aebc0e7-6fd0-4725-9256-04a074ca5683
-- title:
--   Theorem 1.4 — superpolynomial size bounds for depth-3.5 AC0[2]-Frege
-- statement:
--   Let $F$ be a constant-width CNF on $n$ variables with no polynomial-calculus refutation over $\mathbb F_2$ of degree $cn$, and let $G=F\circ\mathrm{Maj}_\ell$ be its majority lift with block length $\ell=\Theta(\log n)$ odd. Then $G$ has polynomial size, and there is a constant $\alpha>0$ such that for all sufficiently large $n$ and all $1\le b\le\sqrt\ell$, every depth-3.5 AC0[2]-Frege refutation of $G$ with bottom degree $b$ has total size $T$ with
--   $$
--   \log T\ \ge\ \alpha\,\frac{(\log n)^{3/2}}{b}.
--   $$
--
--   Precisely: for every $c>0$ and every $0<\lambda_1\le\lambda_2$ there is $\alpha>0$ such that for every width bound $w$ there are $k$ and $n_0$ with the following property. For every $n\ge n_0$, every CNF $F$ on $n$ variables of width at most $w$ with no PC refutation of degree $\lfloor cn\rfloor$, and every odd $\ell$ with $\lambda_1\log n\le\ell\le\lambda_2\log n$:
--
--   1. the encoding length of $G=F\circ\mathrm{Maj}_\ell$ is at most $n^k$, and
--   2. for every $b\ge1$ with $b^2\le\ell$, every depth-3.5 AC0[2]-Frege refutation of $G$ with bottom degree $b$ has total size $T$ with $\log T\ge\alpha(\log n)^{3/2}/b$.
--
--   Since $|G|$ is polynomial in $n$, the bound is superpolynomial in $|G|$ for $b=o(\sqrt{\log n})$ and equals $\exp(\Omega((\log n)^{3/2}))$ for constant $b$. By the normal form of Buss, Kołodziejczyk and Zdanowski, lower bounds for this system with $b=(\log n)^{O(d)}$ would give superpolynomial lower bounds for depth-$d$ AC0[2]-Frege.
--
--   **Formalization Note** The degree hypothesis concerns $F$ in its own $n$ variables (formal PC degree, Boolean axioms included); the refutation is of $G$ in the $N=n\ell$ lifted variables.
--
--   Differences from the source:
--   - generalization: ℓ = Θ(log n) "chosen as in Corollary 4.21" (a sufficiently large constant times log n, rounded up to an odd integer) → for all 0 < λ₁ ≤ λ₂, every odd ℓ with λ₁ log n ≤ ℓ ≤ λ₂ log n, quantified before ∃ α; reason: Corollary 4.21 does not fix its constant; its choice ℓ = ⌈λ log n⌉_odd lies in the window [λ log n, 2λ log n] for large n, so the statement specializes to the source
--   - reading: "a constant α > 0, depending only on c", "for all sufficiently large n", F of constant width → ∃ α after c, λ₁, λ₂ and before the width bound w; ∃ k n₀ after w; reason: constant width fixes w before n; the proof of §5.4 makes α depend only on c and the constant of ℓ = Θ(log n), and n₀ on w
--   - generalization: c in (0, 1) (setting of §4.4); Definition 1.2 says c > 0 → every c > 0; reason: the hypothesis "no PC refutation of degree ⌊cn⌋" is monotone in c, so c ≥ 1 reduces to c = 1/2
--   - reading: "so that G has polynomial size" → a conjunct: ∃ k with encLength (lift F ℓ) ≤ n^k; reason: the sentence asserts that G has polynomial size
--   - encoding: "no PC refutation of degree cn" → ¬ PCDerivable F ⌊c n⌋₊ 1 (formal degree, Boolean axioms y_i² + y_i); reason: formal degrees are integers, so degree ≤ cn means degree ≤ ⌊cn⌋
--   - generalization: lines as disjunctions of terms with weakening and contraction → lines as finite sets of terms (contraction built in); reason: every refutation in the paper's form maps to a set-based one of no larger total size, so the bound specializes
--   - encoding: terms with order and repetition immaterial; polynomials of degree ≤ b; 1 ≤ b ≤ √ℓ; log → terms as finite sets of multilinear MvPolynomial (Fin n × Fin ℓ) (ZMod 2) of totalDegree ≤ b; 1 ≤ b, b² ≤ ℓ; Real.log; reason: same instances; the base of the logarithm is absorbed by α and λ
--   - reading: total size "counts all term occurrences as well as all monomial occurrences" → Σ over lines and their terms of (1 + Σ over the term's polynomials of the number of monomials); reason: one count per term occurrence plus one per monomial occurrence, with nothing else added
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Theorem 1.4, p.5 (restated p.29, (38)); proof §5.4, pp.31–32; Definition 1.2, p.4

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_D35Refutation

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Theorem 1.4, p.5 (restated p.29, (38); proof §5.4, pp.31–32): superpolynomial size
bounds for depth-3.5 AC0[2]-Frege. Let `F` be a constant-width CNF on `n` variables with no PC
refutation of degree `cn`, and let `G = F ∘ Maj_ℓ` with `ℓ = Θ(log n)`, so that `G` has
polynomial size. There is a constant `α > 0` such that for all sufficiently large `n` and all
`1 ≤ b ≤ √ℓ`, every depth-3.5 AC0[2]-Frege refutation of `G` with bottom degree `b` has total
size `T` with `log T ≥ α (log n)^{3/2} / b`.

**Formalization Note** `ℓ = Θ(log n)` is quantified as: for all `0 < λ₁ ≤ λ₂` and every odd `ℓ`
with `λ₁ log n ≤ ℓ ≤ λ₂ log n`; `α` is chosen after `c, λ₁, λ₂` and before the width bound `w`;
`k` (polynomial size) and `n₀` (sufficiently large) after `w`. "No PC refutation of degree
`cn`" is `¬ PCDerivable F ⌊cn⌋ 1` (formal degree, Boolean axioms). `b ≤ √ℓ` is `b² ≤ ℓ`.
`log` is the natural logarithm (the base is absorbed by `α` and `λ`). -/
theorem theorem_1_4_depth35_lower_bound :
    ∀ c : ℝ, 0 < c → ∀ lam₁ lam₂ : ℝ, 0 < lam₁ → lam₁ ≤ lam₂ →
    ∃ α : ℝ, 0 < α ∧ ∀ w : ℕ, ∃ k n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ F : CNF (Fin n), (∀ C ∈ F, C.card ≤ w) → ¬ PCDerivable F ⌊c * n⌋₊ 1 →
    ∀ ℓ : ℕ, Odd ℓ → lam₁ * Real.log n ≤ ℓ → (ℓ : ℝ) ≤ lam₂ * Real.log n →
      encLength (lift F ℓ) ≤ n ^ k ∧
      ∀ b : ℕ, 1 ≤ b → b ^ 2 ≤ ℓ → ∀ π : List (Line (Fin n × Fin ℓ)),
        IsRefutation b (lift F ℓ) π →
          α * Real.log n ^ ((3 : ℝ) / 2) / b ≤ Real.log (totalSize π) := by sorry

end AC02Frege
