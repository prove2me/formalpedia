-- Prove2me | Theorems.Thm_AdamDyn_WellPosed_lemma_7_10
-- name    : AdamDyn.WellPosed.lemma_7_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:39.802288+00:00
-- url     : https://prove2.me/theorems/83f8dde6-d61a-4fcc-b00b-f63abfab1795
-- title:
--   Lemma 7.10 — the family of regularized solutions $(z_\eta)_{\eta>0}$ is equicontinuous
-- statement:
--   Let $a, \varepsilon > 0$ and $0 < b \le 4a$. Let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient (Assumption 7.1) and coercive (Assumption 2.3), and let $S : \mathbb R^d \to \mathbb R^d$ be locally Lipschitz (Assumption 7.2) with $S(x) > 0$ coordinatewise (Assumption 2.4). Let $z_0 \in \mathcal Z_0$, and let $(z_\eta)_{\eta \in (0,+\infty)}$ be any family such that, for every $\eta > 0$, $z_\eta$ is a global solution of $\dot z(t) = h(t+\eta, z(t))$ with initial condition $z_0$, i.e. $z_\eta \in Z^\eta_\infty(z_0)$. Then the family $(z_\eta)_{\eta > 0}$ is equicontinuous on $[0,+\infty)$.
--
--   Together with the uniform bound of Proposition 7.6, this is the hypothesis of the Arzelà–Ascoli theorem used to extract a solution of the Adam equation as a limit of regularized solutions when $\eta \downarrow 0$.
--
--   **Formalization Note.** The family is indexed by the positive reals $\{\eta \in \mathbb R_{\ge 0} : \eta > 0\}$, and equicontinuity is Mathlib's `EquicontinuousOn` on $[0,+\infty)$ (values outside $[0,+\infty)$ play no role).
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 15, Lemma 7.10

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField

open scoped NNReal
open Filter

namespace AdamDyn.WellPosed

/-- Lemma 7.10 (p. 15). Under Assumptions 2.3, 2.4, 7.1, 7.2 and `0 < b ≤ 4a`: for `z0 ∈ 𝒵₀` and any
family `(z_η)_{η > 0}` with `z_η ∈ Z^η_∞(z0)`, the family `(z_η)_{η>0}` is equicontinuous on
`[0, +∞)`. -/
theorem lemma_7_10 {d : ℕ} (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hcoer : Tendsto F (cocompact (Vec d)) atTop)
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (z0 : State d) (hz0 : z0 ∈ Zzero)
    (zfam : {η : ℝ≥0 // 0 < η} → ℝ → State d)
    (hzfam : ∀ η : {η : ℝ≥0 // 0 < η}, IsSolutionOn a b ε F S ((η.1 : ℝ≥0) : WithTop ℝ≥0) ⊤ z0 (zfam η)) :
    EquicontinuousOn zfam (Set.Ici 0) := by sorry

end AdamDyn.WellPosed
