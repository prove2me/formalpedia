-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_sum_bregman
-- name    : BregmanPPA.ProxMult.sum_bregman
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:53.276839+00:00
-- url     : https://prove2.me/theorems/e58f07be-0c17-48ca-a982-3d5f60dc14f7
-- title:
--   Proof of Theorem 8, p. 221 — h_x ⊕ h_p is a Bregman function with zone S_x × S_p ⊇ C × Ω̄⁺ ⊇ cl dom K
-- statement:
--   For a problem of the form (10), let $h_x$ be a Bregman function on $\mathbb R^n$ with zone $S_x\supseteq C$ and $h_p$ a Bregman function on $\mathbb R^m$ with zone $S_p\supseteq\overline{\Omega^+}$. Then $h=h_x\oplus h_p$, $h(x,p)=h_x(x)+h_p(p)$, is a Bregman function on $\mathbb R^{n+m}$ with zone $S_x\times S_p$, and
--
--   $$S_x\times S_p\supseteq C\times\overline{\Omega^+}\supseteq\overline{\operatorname{dom}K}.$$
--
--   Together these give the hypotheses $\overline{S}\supseteq\operatorname{dom}K$ and (C1) $S\supseteq\overline{\operatorname{dom}K}$ under which Theorem 1 is applied to $K$.
--
--   **Formalization Note** $\mathbb R^{n+m}$ is `WithLp 2 (E n × E m)`, where $D_h((x,p),(y,q))=D_{h_x}(x,y)+D_{h_p}(p,q)$. The paper's chain also passes through $\overline{\operatorname{dom}l}$; the statement keeps its two ends, the zone and $\overline{\operatorname{dom}K}$. The paper asserts the Bregman property without proof ("Then $h$ is a Bregman function").
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 221, proof of Theorem 8 (h = h_x ⊕ h_p)

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle

open ThreeOpSplitting.Convergence

namespace BregmanPPA.ProxMult

/-- Proof of Theorem 8, p. 221: `h = h_x ⊕ h_p` is a Bregman function on `ℝⁿ⁺ᵐ` with zone
`S_x × S_p`, and `S_x × S_p ⊇ C × Ω̄⁺ ⊇ cl dom K`. -/
theorem sum_bregman {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp) :
    BregmanPPA.Convergence.IsBregmanFunction (prodZone Sx Sp) (sumFn hx hp) ∧
    closure (dom (opK C f g)) ⊆ prodZone Sx Sp := by sorry

end BregmanPPA.ProxMult
