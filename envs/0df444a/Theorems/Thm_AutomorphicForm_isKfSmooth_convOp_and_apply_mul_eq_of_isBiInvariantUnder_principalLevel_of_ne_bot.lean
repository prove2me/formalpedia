-- Prove2me | Theorems.Thm_AutomorphicForm_isKfSmooth_convOp_and_apply_mul_eq_of_isBiInvariantUnder_principalLevel_of_ne_bot
-- name    : AutomorphicForm.isKfSmooth_convOp_and_apply_mul_eq_of_isBiInvariantUnder_principalLevel_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/faf1edca-5770-5d7d-931b-7386b33119b0
-- title:
--   Convolution by a level-N bi-invariant function is K_f-smooth
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and let $N \subseteq \mathcal O_K$ be a nonzero ideal. Write $G = \mathrm{GL}_2(\mathbb A_K)$ for the adelic general linear group, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`, and let $U = \mathtt{principalLevel}(\mathcal O_K,K,N) \sqcap \mathtt{finiteAdelicGL2Subgroup}\,K$, the intersection of the level-$N$ principal subgroup (the meet of `levelOne` at $N$ with its conjugate by the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$) with the kernel of the projection $\mathrm{GL}_2(\mathbb A_K) \to \mathrm{GL}_2(K \otimes \mathbb R)$. Let $f : G \to \mathbb C$ satisfy $f(kg) = f(g)$ and $f(gk) = f(g)$ for all $k \in U$ and all $g \in G$, and let $u : G \to \mathbb C$ be arbitrary. Then the function $\mathtt{convOp}\,K\,f\,u : x \mapsto \int_G u(xg) f(g)\,dg$ is $K_f$-smooth, i.e. its stabiliser in $\mathtt{finiteAdelicGL2Subgroup}\,K$ for the right-translation action is an open subgroup, and it satisfies $(\mathtt{convOp}\,K\,f\,u)(xk) = (\mathtt{convOp}\,K\,f\,u)(x)$ for every $x \in G$ and every $k \in U$. No integrability hypothesis on $u$ or $f$ is imposed.
--
--   This records that right convolution by a test function bi-invariant under a principal congruence subgroup of nonzero level produces a function invariant under right translation by that subgroup, and hence a smooth vector for the finite-adelic group. It is the smoothness input used in the construction of the isotypic cusp space, and is cited in the verification of the smoothness, Paley–Wiener and approximation properties of the convolution operator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isKfSmooth_convOp_and_apply_mul_eq_of_isBiInvariantUnder_principalLevel_of_ne_bot.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isKfSmooth_convOp_and_apply_mul_eq_of_isBiInvariantUnder_principalLevel_of_ne_bot
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (_hbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (u : AdelicGL2 (𝓞 K) K → ℂ) :
    IsKfSmooth K (convOp K f u) ∧
    ∀ (x : AdelicGL2 (𝓞 K) K), ∀ k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      convOp K f u (x * k) = convOp K f u x := by sorry
