-- Prove2me | Theorems.Thm_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex
-- name    : AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/95f4a4c9-7f65-5dd6-9f78-c6d840e2b6f8
-- title:
--   Derivatives at a complex place pass through Whittaker coefficients
-- statement:
--   Let $K$ be a number field, $D$ an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_K)$ (written `AdelicGL2 (𝓞 K) K`), and $w$ an infinite place of $K$ that is complex. Fix $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ continuous and satisfying `IsArchSmoothAtComplex hw`, i.e. for every $g$ the function $e\mapsto\varphi(g\cdot\mathrm{archComplexLiftAt}\,e)$ on $2\times2$ complex matrices is $C^\infty$ over $\mathbb{R}$ on the locus $\det e\neq0$. Assume moreover that for each of the six directions $d\in\{H,E,F,iH,iE,iF\}$ the function $\mathrm{archDerivAtComplex}\,d\,\varphi$, namely $g\mapsto \frac{d}{dt}\varphi(g\cdot\mathrm{archFlowAtComplex}\,d\,t)|_{t=0}$, is continuous, and that all the second such derivatives $\mathrm{archDerivAtComplex}\,d\,(\mathrm{archDerivAtComplex}\,d'\,\varphi)$ are continuous. Write $W(\psi)(g)=\int \psi(u(x)\,g)\,\chi_K(-x)\,d\nu(x)$ for the Whittaker coefficient at $\alpha=1$ formed from the standard additive character of $\mathbb{A}_K$, the upper unipotent $u(x)$, and the carrier data `productionPinsOf` with window $D$, level subgroups $N\mapsto\mathrm{levelOne}(N)\sqcap$ `finiteAdelicGL2Subgroup`, Hecke generators $v\mapsto\mathrm{heckeGen}(v)$, and $\nu$ the adelic additive Haar measure conditioned on `adelicBox K`. Then for every $g_0\in\mathrm{GL}_2(\mathbb{A}_K)$: for all $d$ and all $h\in\mathrm{GL}_2(\mathbb{C})$, the map $t\mapsto W(\varphi)\bigl(g_0\cdot(h\cdot\mathrm{archFlowMatrixComplex}\,d\,t)_w\bigr)$ has derivative $W(\mathrm{archDerivAtComplex}\,d\,\varphi)(g_0 h_w)$ at $t=0$; and for all $d,d'$ and all $h$, the map $t\mapsto W(\mathrm{archDerivAtComplex}\,d'\,\varphi)\bigl(g_0\cdot(h\cdot\mathrm{archFlowMatrixComplex}\,d\,t)_w\bigr)$ has derivative $W(\mathrm{archDerivAtComplex}\,d\,(\mathrm{archDerivAtComplex}\,d'\,\varphi))(g_0 h_w)$ at $t=0$. Here $(\cdot)_w$ denotes the embedding `archComplexGLAt hw` of $\mathrm{GL}_2(\mathbb{C})$ into $\mathrm{GL}_2(\mathbb{A}_K)$ at the place $w$, and the flows are the diagonal, upper and lower unipotent one-parameter families in $t$ and in $it$.
--
--   This is the statement that right differentiation along the six real one-parameter subgroups of $\mathrm{SL}_2(\mathbb{C})$ commutes with the Whittaker integral at a complex place, to first and second order — differentiation under the integral sign over the conditioned adelic box. It supplies the regularity input for the analysis of Whittaker coefficients of Casimir eigenfunctions at a complex place, and is used in [`AutomorphicForm.whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses`](thm.html#AutomorphicForm.whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses) and in the resulting decay estimate [`AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String`](thm.html#AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ) (hφs : IsArchSmoothAtComplex hw φ)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d φ))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' φ)))
    (g₀ : AdelicGL2 (𝓞 K) K) :
    (∀ (d : ArchDirComplex) (h : GL (Fin 2) ℂ),
        HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (φ) 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d t)))
          (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d φ) 1 (g₀ * archComplexGLAt hw h)) 0) ∧
    (∀ (d d' : ArchDirComplex) (h : GL (Fin 2) ℂ),
        HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d' φ) 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d t)))
          (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (archDerivAtComplex hw d' φ)) 1 (g₀ * archComplexGLAt hw h)) 0) := by sorry
