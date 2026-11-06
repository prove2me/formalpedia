-- Prove2me | Theorems.Thm_BianchiIX_gaussWord_diameter
-- name    : BianchiIX.gaussWord_diameter
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:10:58.320455+00:00
-- url     : https://prove2.me/theorems/66733fad-b4ef-4b85-b112-a20022cc2050
-- title:
--   Diameter bound for Gauss cylinders
-- statement:
--   Write $g_a(x)=1/(a+x)$. For a finite word
--   $w=(a_0,\ldots,a_{k-1})$ of natural numbers, let
--   $$G_w=g_{a_0}\circ\cdots\circ g_{a_{k-1}},\qquad G_{\varnothing}(x)=x.$$
--
--   If every digit in $w$ is at least $1$, then for $x,y\in[0,1]$,
--   $$|G_w(x)-G_w(y)|\leq4^{-\lfloor |w|/2\rfloor}.$$
--   Thus the image of the unit interval under an inverse word has exponentially
--   small diameter in the word length.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussInverse.lean#L120-L127

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section
open Filter
open scoped Topology

theorem BianchiIX.gaussWord_diameter (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |gaussWord w x - gaussWord w y| ≤ (1 / 4 : ℝ) ^ (w.length / 2) := by sorry
