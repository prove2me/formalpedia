-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctions_Quasi_qsb_implication_chain
-- name    : DiscreteConvex.LConvexFunctions.Quasi.qsb_implication_chain
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:17:49.65772+00:00
-- url     : https://prove2.me/theorems/181b565a-24c3-4d7e-aac9-9fa6cccfe82a
-- title:
--   Theorem 7.49 -- the quasi-submodularity nesting chain
-- statement:
--   **Theorem 7.49** (p.199). (1) The implications (SBF[Z]) $\Rightarrow$ (SSQSB) $\Rightarrow$ (QSB), (SSQSB) $\Rightarrow$ (SSQSBw) $\Rightarrow$ (QSBw), and (QSB) $\Rightarrow$ (QSBw) all hold. (2) $g$ satisfies (SBF[Z]) if and only if every linear perturbation $g[x]$ satisfies (QSBw). Part (2) precisely quantifies how much weaker (QSBw) is than plain submodularity pointwise, while showing the gap closes once (QSBw) is required for *every* perturbation — the direct analogue of chunk 07's Theorem 6.68 for the L-convex side.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, Theorem 7.49.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, Theorem 7.49

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_QSB
import Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_SSQSB
import Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_QSBw
import Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_SSQSBw
import Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_PerturbedL

open DiscreteConvex.LConvexFunctions

namespace DiscreteConvex.LConvexFunctions.Quasi

/-- Theorem 7.49 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.199). (1) The
implications (SBF[Z]) ⟹ (SSQSB) ⟹ (QSB), (SSQSB) ⟹ (SSQSBw) ⟹ (QSBw), and (QSB) ⟹ (QSBw) all
hold. (2) `g` satisfies (SBF[Z]) if and only if every linear perturbation `g[x]` satisfies
(QSBw). Part (2) shows exactly how much weaker (QSBw) is pointwise than (SBF[Z]), and that the
gap closes once (QSBw) is required for every perturbation. -/
theorem qsb_implication_chain {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ) :
    (SBF g → SSQSB g) ∧ (SSQSB g → QSB g) ∧ (SSQSB g → SSQSBw g) ∧ (QSB g → QSBw g) ∧
      (SSQSBw g → QSBw g) ∧ (SBF g ↔ ∀ x : V → ℝ, QSBw (PerturbedL g x)) := by sorry

end DiscreteConvex.LConvexFunctions.Quasi
