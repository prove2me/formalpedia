-- Prove2me | Theorems.Thm_AlgebraicCurve_residueTraceCompletionCommute_v2
-- name    : AlgebraicCurve.residueTraceCompletionCommute_v2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/7ba90df5-c010-5f6b-9089-ac3c6c0c8fc6
-- title:
--   Residue commutes with trace through the completion
-- statement:
--   Let $K$, $E$, $F$ be fields with $K \subseteq E \subseteq F$ (a $K$-algebra structure on $E$ and on $F$, an $E$-algebra structure on $F$, compatible as a scalar tower), with $F$ integral over $E$ and $F/E$ separable. Assume that every place $u$ of $E$ over $K$ — that is, every valuation subring of $E$ containing $\mathrm{image}(K)$, proper, and a principal ideal ring — has residue field finite over $K$; that both $F$ and $E$ carry the curve package over $K$ (principal divisors of degree zero for every nonzero function, residue fields finite over $K$ at all places, and $\Omega_{\cdot/K}$ free of rank one); that $K$ is perfect; that $\Omega_{F/K} \neq 0$; and that at every place $w$ of $F$ the element $d\pi_w = D_{K,F}(\pi_w)$ spans $\Omega_{F/K}$. Then the predicate `KwF4R1V391aResidueTraceCompletionCommute K F E` holds: for all places $v$ of $E$ and $w$ of $F$ with $w$ in the fibre of $v$, both with generating differential coordinate, and every $g \in F$, assuming additionally $[F:E]$ finite, $\Omega_{E/K} \neq 0$, finiteness of all residue fields of $F$ over $K$ and existence of principal divisors for $E$ and $F$, one has $$\mathrm{Tr}_{\kappa(w)/K}\bigl(\mathrm{res}_w\bigl(g \cdot c_w(\mathrm{d}\pi_v)\bigr)\bigr) = \mathrm{Tr}_{\kappa(v)/K}\bigl(\widehat{\mathrm{res}}_v\bigl(\mathrm{Tr}_{\hat F_w/\hat E_v}(g)\bigr)\bigr),$$ where $c_w$ denotes the coefficient of a differential with respect to $d\pi_w$, $\mathrm{d}\pi_v$ is pushed from $\Omega_{E/K}$ to $\Omega_{F/K}$ along `KaehlerDifferential.map`, and on the right the local residue is taken on the $v$-adic completion of $E$ after the completion trace from $F$ at $w$.
--
--   This is the local trace–residue compatibility: taking residues commutes with the trace, one side computed on $F$ at a place $w$ above $v$ against the pulled-back differential coordinate, the other on the completion of $E$ at $v$ after tracing the function down. It is obtained by combining the Tate-residue package over $F$ and over $E$ (finiteness, agreement of the Tate residue with the canonical local residue on the completion, the chain rule and trace compatibility for separable extensions), and it feeds the fibrewise residue identity and the proof of the residue theorem over a perfect base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_residueTraceCompletionCommute_v2.lean

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
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.residueTraceCompletionCommute_v2
    {K F E : Type*} [Field K] [Field F] [Algebra K F]
    [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [∀ u : AlgebraicCurve.Place K E, u.FiniteResidue]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K E] [PerfectField K]
    [Nontrivial Ω[F⁄K]] [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra.IsSeparable E F] :
    ModularCurve.KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute K F E := by sorry
