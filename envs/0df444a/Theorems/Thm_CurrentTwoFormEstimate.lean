-- Prove2me | Theorems.Thm_CurrentTwoFormEstimate
-- name    : CurrentTwoFormEstimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:59:59.108863+00:00
-- url     : https://prove2.me/theorems/8ea34214-afae-5fd0-b55e-f303b85027dc
-- title:
--   Current Two Form Estimate: Current Two Form Estimate
-- statement:
--   Paper.tex 1398-1407: the two-step multilinearity split of
--   `[[γ]](f,π) - [[γ]](f_k,π_j)` into `[[γ]](f-f_k,π) + [[γ]](f_k,π-π_j)`, followed by the two
--   Lemma A.2 estimates, packaged as a single per-curve bound by `ψ̃ + ψ`. Here `ω = (f,π)` is the
--   ambient `1`-form, `ωk = (f_k,π)` replaces only the `f`-slot, and `ωkj = (f_k,π_j)` replaces both;
--   the hypotheses say exactly that (`ωkj.f = ωk.f`, `ωk.pi = ω.pi`), that all six bound/Lipschitz
--   fields in play are `≤ C`, and that `f_k` (resp. `π_j`) is `ε`-close to `f` (resp. `π`) on the
--   finite set `Q`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentTwoFormEstimate.lean#L17-L57
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentTwoFormEstimate.lean#L17-L57

import Definitions.Def_Tablet_CurrentFormAddF
import Definitions.Def_Tablet_CurrentFormAddPi
import Definitions.Def_Tablet_PiBoundsF
import Definitions.Def_Tablet_PiBoundsPi
import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurrentTwoFormEstimate
import Theorems.Thm_CurrentFormAddF
import Theorems.Thm_CurrentFormAddPi
import Theorems.Thm_PiBoundsF
import Theorems.Thm_PiBoundsPi

set_option autoImplicit false

theorem CurrentTwoFormEstimate {E : Type*} [MetricSpace E] (γ : Curve E) (m : ℕ) (hm : 1 ≤ m)
    (Q : Finset E) (hQne : Q.Nonempty) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (ω ωk ωkj : Form1 E)
    (hfk : ωkj.f = ωk.f) (hpik : ωk.pi = ω.pi)
    (hfB : (ω.fBound : ℝ) ≤ C) (hfBk : (ωk.fBound : ℝ) ≤ C)
    (hfL : (ω.fLip : ℝ) ≤ C) (hfLk : (ωk.fLip : ℝ) ≤ C)
    (hpL : (ω.piLip : ℝ) ≤ C) (hpLk : (ωk.piLip : ℝ) ≤ C) (hpLkj : (ωkj.piLip : ℝ) ≤ C)
    (hQf : ∀ q ∈ Q, |ω.f q - ωk.f q| ≤ ε)
    (hQpi : ∀ q ∈ Q, |ω.pi q - ωkj.pi q| ≤ ε) :
    |curveCurrent γ ω - curveCurrent γ ωkj| ≤ psiTilde m Q ε C γ + psi m Q ε C γ := by sorry
