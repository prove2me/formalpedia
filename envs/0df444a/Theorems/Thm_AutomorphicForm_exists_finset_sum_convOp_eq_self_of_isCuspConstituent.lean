-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_sum_convOp_eq_self_of_isCuspConstituent
-- name    : AutomorphicForm.exists_finset_sum_convOp_eq_self_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/7cdb0e44-67a3-591d-8ef9-6af8ce7e4cfa
-- title:
--   Finite convolution combination acting as identity on a cuspidal constituent
-- statement:
--   Let $K \subseteq L$ be number fields, let $c,u,d_1,d_2$ be real numbers with $d_1 < d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_L)$. Write $\Omega = \bigcup_{x \in T} \{g x : g \in \Sigma\}$, where $\Sigma$ is the centre-cut Siegel set of parameters $(c,u,d_1,d_2)$: the set of $g$ whose finite part lies in the integral subset `finiteIntegralGL2` and whose archimedean component satisfies $c \le \mathrm{localHeight}$, $\mathrm{xWindowSq} \le u^2$ and $\mathrm{archDetNorm}_w(g) \in [d_1,d_2]$ at every infinite place $w$. Assume $\Omega$ covers modulo the centre, i.e. for every $g$ there are $\gamma \in \mathrm{GL}_2(L)$ and $z \in \mathbb{A}_L^\times$ with $\gamma g z \in \Omega$. Let `pins` be the carrier pins on $L$ built from $\Omega$, the Borel structure and adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$, full centre group $Z = \top$, the level family $N \mapsto \mathrm{levelOne}(N) \cap \ker(\mathrm{glArch})$, the Hecke generators $v \mapsto \mathrm{heckeGen}(v)$, and the additive Haar measure conditioned on the adelic box; let $\xi : Z \to \mathbb{C}^\times$ be a character. Let $N_K \ne 0$ be an ideal of $\mathcal{O}_K$, $S_K$ a finite set of height-one primes of $K$ containing every prime dividing $N_K$, and $\mathrm{tys}$ an archimedean type family of $L$ (a number of types at each infinite place together with representations realising them). Let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ which is a cusp constituent for `pins` and $\xi$: it satisfies `IsCuspSubrep`, is non-zero, and every `IsCuspSubrep` submodule contained in it is $0$ or $V$. Then there exist a finite set $s$ of functions $\mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ and scalars $a_\varphi$ such that each $\varphi \in s$ is continuous with compact support and satisfies `IsUnitFactorizableAboveOfType` for $K \subseteq L$, the type family $\mathrm{tys}$, the group $\mathrm{levelOne}(N_K \mathcal{O}_L) \cap \ker(\mathrm{glArch})$ and the set $S_K$ (that is, `IsUnitFactorizableAbove` together with `IsArchBiFinite`), and such that $\sum_{\varphi \in s} a_\varphi \cdot (\mathrm{convOp}\,\varphi)(y) = y$ for every $y$ lying in the intersection of $V$, the submodule of functions invariant under right translation by $\mathrm{levelOne}(N_K \mathcal{O}_L) \cap \ker(\mathrm{glArch})$, and the archimedean cut submodule attached to $\mathrm{tys}$; here $\mathrm{convOp}\,\varphi$ sends $y$ to the right convolution $\mathrm{rightConv}\,y\,\varphi$.
--
--   This is the statement that on the finite-dimensional space of vectors of fixed level $N_K\mathcal{O}_L$ and prescribed archimedean types inside a cuspidal constituent of $\mathrm{GL}_2$ over $L$, a single finite linear combination of convolution operators by test functions factorizable above $S_K$ acts as the identity — an explicit substitute for an idempotent in the Hecke algebra of that level and type. It is used by [`AutomorphicForm.exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero`](thm.html#AutomorphicForm.exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero), which extracts from it a single test function whose convolution operator is non-zero on a prescribed vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_sum_convOp_eq_self_of_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_finset_sum_convOp_eq_self_of_isCuspConstituent
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (hNK : NK ≠ ⊥) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent L
      (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ V) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
          (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
        Continuous φ ∧ HasCompactSupport φ) ∧
      ∀ y ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys,
        ∑ φ ∈ s, a φ • convOp L φ y = y := by sorry
