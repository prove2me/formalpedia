-- Prove2me | Theorems.Thm_AC02Frege_proposition_5_2_preservation
-- name    : AC02Frege.proposition_5_2_preservation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:17.830326+00:00
-- url     : https://prove2.me/theorems/07f22a6f-9686-472e-8e2b-3868065ac7df
-- title:
--   Proposition 5.2 — preservation of the rules
-- statement:
--   Let $\ell$ be odd, $F$ a CNF, $G=F\circ\mathrm{Maj}_\ell$, and let $\pi$ be a depth-3.5 AC0[2]-Frege refutation of $G$ with bottom degree $b$. Choose approximants $A_{\mathcal T}$, $P_L$ of the shape of Definition 5.1 with $t_{in},t_{out}\ge1$ factors, and put $R=bt_{in}$. Suppose $\beta(f)\le Q$, both error families (39) and (40) hold, and
--   $$
--   Q+\max\{2Rt_{out}+2R,\ Rt_{out}+w(G)\}\le D,\qquad Q+2w(F)\le D.\tag{41}
--   $$
--   Then every line $L$ of the refutation satisfies $fP_L\in\widehat C_D$. The empty final line consequently gives $f\in\widehat C_D$.
--
--   This is the simulation step: the rules of the proof system force the corrected approximants, and finally the multiplier itself, into $\widehat C_D$.
--
--   Differences from the source:
--   - encoding: ℓ odd, m = (ℓ − 1)/2 (standing assumption of §4) → hypothesis Odd ℓ, m = ℓ / 2; reason: same instances
--   - encoding: polynomials over F2 identified with functions on the cube; products of functions → MvPolynomial over ZMod 2; products multilinearized by ML (membership in Ĉ_D and β depend only on ML p); reason: Definition 2.1 identifies a function with its multilinear polynomial; no instance changes
--   - generalization: the standing setting of §5 (p.28): F of constant width with no PC refutation of degree D = ⌊cn⌋, ℓ = Θ(log n), Q = ⌊cn/16⌋ → any CNF F, any odd ℓ, any D and Q subject only to the printed hypotheses β(f) ≤ Q, (39), (40), (41); reason: the proof (App. D, pp.48–49) uses only these hypotheses, never 1 ∉ C_D, the width of F or the size of ℓ; at the section's values the statement is the source's
--   - encoding: lines as disjunctions with weakening and contraction → lines and terms as finite sets (IsRefutation); reason: contraction is implicit; same refutations up to contraction
--   - encoding: approximants of the shape of Definition 5.1 → an Approx structure of coefficients; A_T and P_L multilinearized; reason: same approximants as functions
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Proposition 5.2, (41), p.30; proof App. D, pp.48–49

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

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Proposition 5.2, (41), p.30 (preservation of the rules; proof App. D, pp.48–49): let
`π` be a depth-3.5 AC0[2]-Frege refutation of `G = F ∘ Maj_ℓ` with bottom degree `b`, and choose
approximants of the shape of Definition 5.1 with `t_in, t_out ≥ 1` factors and `R = b t_in`.
Suppose `β(f) ≤ Q`, both error families (39), (40) hold, and
`Q + max{2R t_out + 2R, R t_out + w(G)} ≤ D`, `Q + 2w(F) ≤ D` (41). Then every line `L` of the
refutation satisfies `f P_L ∈ Ĉ_D`; the empty final line consequently gives `f ∈ Ĉ_D`.

**Formalization Note** `ℓ` odd; `w(·)` is `width`; products are products of functions. -/
theorem proposition_5_2_preservation {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (b D Q tin tout : ℕ) (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (π : List (Line (Fin n × Fin ℓ))) (hπ : IsRefutation b (lift F ℓ) π)
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hf : coeffDeg f ≤ (Q : WithBot ℕ)) (h39 : InnerErr F ℓ D Φ π f)
    (h40 : OuterErr F ℓ D Φ π f)
    (h41a : Q + max (2 * (b * tin) * tout + 2 * (b * tin)) (b * tin * tout + width (lift F ℓ))
      ≤ D)
    (h41b : Q + 2 * width F ≤ D) :
    (∀ L ∈ π, f * Φ.P L ∈ CHat F ℓ D) ∧ f ∈ CHat F ℓ D := by sorry

end AC02Frege
