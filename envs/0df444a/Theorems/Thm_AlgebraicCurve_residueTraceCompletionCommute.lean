-- Prove2me | Theorems.Thm_AlgebraicCurve_residueTraceCompletionCommute
-- name    : AlgebraicCurve.residueTraceCompletionCommute
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/f37f0322-59b0-5873-9a86-0b6e6e89bd53
-- title:
--   Residue–trace commutation through the completion, F/E separable
-- statement:
--   Let $K\subseteq E\subseteq F$ be fields with $E$ and $F$ both $K$-algebras and $F$ an $E$-algebra forming a scalar tower over $K$, with $F$ integral over $E$ and $F/E$ separable. Assume every place $u$ of $E$ over $K$ has residue field finite over $K$, that both $F$ and $E$ carry the curve package `IsCurveOver K ·` (principal divisors of degree zero for every nonzero element, residue fields finite over $K$ at all places, and $\Omega_{\cdot/K}$ free of rank one), that $K$ is perfect, that $\Omega_{F/K}\ne 0$, and that at every place $w$ of $F$ the differential $d\pi_w$ of a uniformiser spans $\Omega_{F/K}$. The conclusion is the proposition `KwF4R1V391aResidueTraceCompletionCommute K F E`, which internally quantifies over the instance hypotheses that $E$ and $F$ have principal divisors, that all places of $F$ have $K$-finite residue fields, that $F$ is finite-dimensional over $E$ and $\Omega_{E/K}\ne 0$, and asserts: for every place $v$ of $E$ with $d\pi_v$ spanning $\Omega_{E/K}$, every place $w$ of $F$ with $d\pi_w$ spanning $\Omega_{F/K}$ lying in the fibre of $v$, and every $g\in F$, the residue term at $w$ of the pullback of $d\pi_v$ along $\Omega_{E/K}\to\Omega_{F/K}$ against the constant family $g$ — that is, $\mathrm{Tr}_{\kappa(w)/K}$ of the local residue at $w$ of $g$ times the `differentialCoeff` of that pulled-back differential — equals $\mathrm{Tr}_{\kappa(v)/K}$ of the value obtained by applying the local residue at $v$ to an element of $E$ differing from the completed trace $\mathrm{Tr}_{\hat F_w/\hat E_v}(g)\in\hat E_v$ by an element of the valuation ring of $\hat E_v$.
--
--   This is the local trace–residue compatibility: residues commute with the trace from $F$ to $E$, computed through the completions at a place and the places above it. It is assembled from the finiteness, agreement, chain-rule and trace-compatibility statements for Tate's residue, and feeds the $K$-valued residue theorem for function fields obtained by transporting the residue theorem on $\mathbf{P}^1$ along a cotrace.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_residueTraceCompletionCommute.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.Def_AlgebraicCurve_PlaceCompletion
import Definitions.Def_AlgebraicCurve_TateResidueCurrency
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.residueTraceCompletionCommute
    {K F E : Type*} [Field K] [Field F] [Algebra K F]
    [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [∀ u : AlgebraicCurve.Place K E, u.FiniteResidue]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K E] [PerfectField K]
    [Nontrivial Ω[F⁄K]] [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra.IsSeparable E F] :
    ModularCurve.KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute K F E := by sorry
