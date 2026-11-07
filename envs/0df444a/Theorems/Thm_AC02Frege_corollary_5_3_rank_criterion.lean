-- Prove2me | Theorems.Thm_AC02Frege_corollary_5_3_rank_criterion
-- name    : AC02Frege.corollary_5_3_rank_criterion
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:14.68403+00:00
-- url     : https://prove2.me/theorems/838e7c6a-f56e-4885-93f0-55392db576b4
-- title:
--   Corollary 5.3 — the combined rank criterion
-- statement:
--   Let $\ell$ be odd, $N=n\ell$, $G=F\circ\mathrm{Maj}_\ell$, and let $\pi$ be a depth-3.5 AC0[2]-Frege refutation of $G$ with bottom degree $b$ and total size $T$. Let $t_{in},t_{out}\ge1$, $R=bt_{in}$, and $\eta(d)=\tfrac12M_N(K-d)/M_N(K)$. Assume $R\le K<N/2$ and (41). Then:
--
--   1. The approximants can be chosen so that all error conditions (39) and (40), together with $f\in W_Q$, have combined rank (codimension in $V_K(x)$ of their common solution space) at most
--   $$
--   T\bigl(e^{-\eta(b)t_{in}}+e^{-\eta(R)t_{out}}\bigr)\bigl(h+\varepsilon M_N(K)\bigr)+2TN^2\varepsilon M_N(K)\bigl(\eta(b)^{-1}+\eta(R)^{-1}\bigr)+E_K.\tag{42}
--   $$
--   2. If this is less than $h$, such a refutation cannot exist; that is, $h$ is at most (42).
--
--   This is the counting half of the lower bound; Section 5.4 chooses the parameters so that (42) is below $h$ for small refutations.
--
--   Differences from the source:
--   - encoding: ℓ odd, m = (ℓ − 1)/2 (standing assumption of §4) → hypothesis Odd ℓ, m = ℓ / 2; reason: same instances
--   - encoding: polynomials over F2 identified with functions on the cube; products of functions → MvPolynomial over ZMod 2; products multilinearized by ML (membership in Ĉ_D and β depend only on ML p); reason: Definition 2.1 identifies a function with its multilinear polynomial; no instance changes
--   - generalization: the standing setting of §5 (p.28): F of constant width with no PC refutation of degree D = ⌊cn⌋, ℓ = Θ(log n), Q = ⌊cn/16⌋, K = ⌊N/2 − an√ℓ⌋ → any CNF F, any odd ℓ, any D, Q, K subject only to the printed hypotheses R ≤ K < N/2 and (41); reason: the proof (Prop 4.17 for each term and line, the rank count, Prop 5.2) uses only these hypotheses, never 1 ∉ C_D; at the section's values the statement is the source's
--   - encoding: "combined rank" → M_N(K) − finrank of the span of {f ∈ V_K(x) ∩ W_Q : (39), (40) for π}; reason: the codimension of the common solution space in V_K(x)
--   - encoding: "if (42) < h, such a refutation cannot exist" → h ≤ (42) for every refutation satisfying the hypotheses; reason: contrapositive
--   - encoding: lines as disjunctions with weakening and contraction → lines and terms as finite sets (IsRefutation); reason: contraction is implicit; total size counts term and monomial occurrences as in Definition D.1
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Corollary 5.3, (42), p.31

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_D35Refutation
import Definitions.Def_AC02Frege_majorityExpansion
import Definitions.Def_AC02Frege_rankCounts
import Definitions.Def_AC02Frege_approximants

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Corollary 5.3, (42), p.31 (the combined rank criterion): for a depth-3.5 AC0[2]-Frege
refutation `π` of `G = F ∘ Maj_ℓ` with bottom degree `b` and total size `T`, assume
`R ≤ K < N/2` (`R = b t_in`) and (41). Then (a) the approximants (Definition 5.1, `t_in` inner and
`t_out` outer factors) can be chosen so that all error conditions (39), (40), together with
`f ∈ W_Q`, have combined rank at most
`T (e^{−η(b) t_in} + e^{−η(R) t_out}) (h + ε M_N(K)) + 2 T N² ε M_N(K) (η(b)^{−1} + η(R)^{−1}) + E_K`
(42); and (b) if this is less than `h`, such a refutation cannot exist, i.e. `h ≤ (42)`.

**Formalization Note** `ℓ` odd, `N = nℓ`, `η(d) = etaFrac N K d`. The combined rank is the
codimension `M_N(K) − dim` of the common solution space `{f ∈ V_K(x) ∩ W_Q : (39), (40)}` in
`V_K(x)`. -/
theorem corollary_5_3_rank_criterion {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (b D Q K tin tout : ℕ) (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (π : List (Line (Fin n × Fin ℓ))) (hπ : IsRefutation b (lift F ℓ) π)
    (hRK : b * tin ≤ K) (hKN : 2 * K < n * ℓ)
    (h41a : Q + max (2 * (b * tin) * tout + 2 * (b * tin)) (b * tin * tout + width (lift F ℓ))
      ≤ D)
    (h41b : Q + 2 * width F ≤ D) :
    let N := n * ℓ
    let T : ℝ := (totalSize π : ℝ)
    let h : ℝ := (hThresh F ℓ D K : ℝ)
    let ε : ℝ := epsExcl n ℓ Q K
    let M : ℝ := (monoCount N K : ℝ)
    let ηb : ℝ := etaFrac N K b
    let ηR : ℝ := etaFrac N K (b * tin)
    let bound : ℝ := T * (Real.exp (-(ηb * tin)) + Real.exp (-(ηR * tout))) * (h + ε * M)
      + 2 * T * (N : ℝ) ^ 2 * ε * M * (ηb⁻¹ + ηR⁻¹) + (Eexcl n ℓ Q K : ℝ)
    (∃ Φ : Approx (Fin n × Fin ℓ) tin tout,
      M - (dimSpan {f | f ∈ Vdeg (Fin n × Fin ℓ) K ∧ f ∈ WQ n ℓ Q ∧
        InnerErr F ℓ D Φ π f ∧ OuterErr F ℓ D Φ π f} : ℝ) ≤ bound) ∧
    h ≤ bound := by sorry

end AC02Frege
