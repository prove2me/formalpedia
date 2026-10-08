-- Prove2me | Theorems.Thm_BigDataNV_Reg_nvCost_sigmaAdmissible
-- name    : BigDataNV.Reg.nvCost_sigmaAdmissible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:53:16.923921+00:00
-- url     : https://prove2.me/theorems/d436016a-81ae-4c59-b4f3-825d21fc3c2f
-- title:
--   (31), p. 31 — the newsvendor cost is (b∨h)-admissible
-- statement:
--   Let $b,h>0$ and let $C(q;d)=b(d-q)^+ + h(q-d)^+$ be the newsvendor cost. For any class $\mathcal F$ of real-valued decision rules on a feature domain $\mathcal X$, the cost $C$ is **$(b\vee h)$-admissible** with respect to $\mathcal F$: the constant $b\vee h$ is nonnegative, $q\mapsto C(q;d)$ is convex for every demand $d$, and
--   $$|C(y_1;d)-C(y_2;d)|\le (b\vee h)\,|y_1-y_2|$$
--   for all predictions $y_1,y_2$ attainable by rules of $\mathcal F$ and all demands $d$.
--
--   In particular this holds for the class of linear rules $q(x)=q^\top x$ used by (NV-reg). It is the hypothesis under which the stability theorem for regularization in a reproducing kernel Hilbert space (Theorem 5) applies, with $\sigma=b\vee h$.
--
--   **Formalization Note** The statement uses the published notion of $\sigma$-admissibility (Bousquet and Elisseeff's Definition 19, restated as Definition 2 on p. 31), which also requires $\sigma\ge0$. Display (29) prints $|q_1-q_2|$ on the right where $|y_1-y_2|$ is meant. The statement is made for every class of rules, which contains the paper's class $\mathcal Q$ of linear rules.
-- source:
--   Rudin & Vahn, The Big Data Newsvendor: Practical Insights from Machine Learning, MIT Sloan Working Paper 5036-13 (version of February 6, 2014), p. 31, proof of Theorem 4, display (31); Definition 2, display (29)

import Mathlib
import Definitions.Def_BigDataNV_Reg_Setting

namespace BigDataNV.Reg

/-- Display (31), proof of Theorem 4, p. 31: the newsvendor cost is `(b ∨ h)`-admissible
(Definition 2, p. 31), for every class `F` of real-valued decision rules on any feature domain,
in particular for the linear rules `Q`. -/
theorem nvCost_sigmaAdmissible (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    {X : Type*} (F : Set (X → ℝ)) :
    StabGen.RKHS.SigmaAdmissible F (nvCost b h) (max b h) := by sorry

end BigDataNV.Reg
