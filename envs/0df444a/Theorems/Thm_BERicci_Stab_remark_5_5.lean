-- Prove2me | Theorems.Thm_BERicci_Stab_remark_5_5
-- name    : BERicci.Stab.remark_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:11.730706+00:00
-- url     : https://prove2.me/theorems/091e1251-66a2-490f-8609-0d334f8504fb
-- title:
--   Remark 5.5 — Cheeger energy is invariant under an isometric embedding
-- statement:
--   Let $\iota:X\to Z$ be an isometric embedding of a complete separable metric space into a complete separable metric space, let $m\in\mathcal P_2(X)$ (the situation of Definition 5.4), and write $\tilde m=\iota_\#m$. For every $f\in L^2(Z,\tilde m)$,
--
--   $$\widetilde{\mathcal E}(f)=\mathcal E(f\circ\iota),\qquad \mathcal E=2\operatorname{Ch}_m,\quad\widetilde{\mathcal E}=2\operatorname{Ch}_{\tilde m}.$$
--
--   This identity lets the stability argument pass between a varying-space formulation and an ambient realization of SGH convergence.
-- source:
--   arXiv:1209.5786v4, Remark 5.5, pp. 63–64, displayed Cheeger-energy identity

import Mathlib
import Definitions.Def_BERicci_Stab_Convergence

namespace BERicci.Stab

open MeasureTheory

/-- Remark 5.5, pp. 63–64: Cheeger energy is invariant under an isometric embedding, in the situation
of Definition 5.4 (`m ∈ P₂(X)`). -/
theorem remark_5_5 {X Z : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [CompleteSpace Z] [SecondCountableTopology Z]
    (m : Measure X) (hm : BERicci.Gamma.InP2 m) (ι : X → Z) (hι : Isometry ι)
    (f : Z → ℝ) (hf : MemLp f 2 (m.map ι)) :
    limitEnergy (m.map ι) f = limitEnergy m (f ∘ ι) := by sorry

end BERicci.Stab
