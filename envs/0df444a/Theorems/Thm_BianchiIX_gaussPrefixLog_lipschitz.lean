-- Prove2me | Theorems.Thm_BianchiIX_gaussPrefixLog_lipschitz
-- name    : BianchiIX.gaussPrefixLog_lipschitz
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:24:42.590489+00:00
-- url     : https://prove2.me/theorems/a41cb62d-38d4-4af3-a1b8-df78ab8009a8
-- title:
--   Uniform Lipschitz bound for the logarithmic prefix derivative
-- statement:
--   Let $a=(a_j)_{j\geq0}$ be positive integers and write
--   $g_b(x)=1/(b+x)$ and $G_n=g_{a_0}\circ\cdots\circ g_{a_{n-1}}$, with $G_0$ the identity.
--   Define $q_{-1}=0$, $q_0=1$, and $q_{n+1}=a_nq_n+q_{n-1}$. Set
--   $$Q_n(x)=q_n+q_{n-1}x,\qquad L_n(x)=-2\log Q_n(x).$$
--   For every $n\geq0$ and $x,y\geq0$,
--   $$|L_n(x)-L_n(y)|\leq2|x-y|.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussDistortion.lean#L111-L133

import Definitions.Def_BianchiIX_Statistics_GaussDistortion
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open BianchiIX
noncomputable section
open Set Finset

theorem BianchiIX.gaussPrefixLog_lipschitz (a : ℕ → ℕ+) (n : ℕ)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussPrefixLog a n x - gaussPrefixLog a n y| ≤ 2 * |x - y| := by sorry
