-- Prove2me | Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
-- name    : AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/8bd1b687-2d60-5640-816e-0d5b5cf62589
-- title:
--   Riemann–Roch from the residue theorem, K algebraically closed
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure, and suppose in addition that $F$ is an algebra over $\mathrm{RatFunc}\,K$ compatibly with $K$ (scalar tower), integral, finite and separable over $\mathrm{RatFunc}\,K$. The remaining hypotheses are: `HasCanonicalDivisor`, i.e. for each nonzero $\omega \in \Omega_{F/K}$ there is a finitely supported $\mathbb Z$-valued function on the places of $F/K$ whose value at each place $v$ is $\mathrm{ord}_v(\omega)$; at every place $v$ of $F/K$ and of $\mathrm{RatFunc}\,K/K$ the element $d\,(\text{uniformiser})$ spans the relevant module of differentials over the field and the residue field is finite over $K$; $\Omega_{F/K}$ and $\Omega_{\mathrm{RatFunc}\,K/K}$ are nontrivial; `IsCurveOver K F` and `IsCurveOver K (RatFunc K)` (principal divisors exist and have degree $0$, residue fields are finite over $K$, and the module of differentials is free of rank one); `HasPrincipalDivisors K F`; existence of local residue data at every place, together with a chosen family of canonical local residue data over $K$; and `HasSeparableResidue K F`, i.e. the trace $\mathrm{Tr}_{\,\kappa(v)/K}$ is nonzero for every place $v$. Assume finally `ResidueTheoremK K F`: for every family of canonical local residue data, every nonzero $\omega$ and every $f \in F$, the associated Weil functional vanishes on the diagonal adele of $f$. Then `FunctionFieldRiemannRoch K F` holds: for every nonzero $\omega \in \Omega_{F/K}$ and every divisor $D$, $$\ell(D) - \ell\big((\omega) - D\big) = \deg D + 1 - g,$$ where $(\omega)$ is the canonical divisor attached to $\omega$ and $g$ is `genus K F`, defined as $\lfloor(\deg(\omega)+2)/2\rfloor$ for a chosen nonzero differential.
--
--   This is the Riemann–Roch theorem for a function field $F$ over an algebraically closed constant field $K$, obtained from the residue theorem by the adelic (Weil–Tate) route. It is the form in which Riemann–Roch enters the arithmetic of modular curves; it is used by [`AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed`](thm.html#AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed), where the residue theorem hypothesis is itself discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean

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
import Definitions.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F]
    (hRTK : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F := by sorry
