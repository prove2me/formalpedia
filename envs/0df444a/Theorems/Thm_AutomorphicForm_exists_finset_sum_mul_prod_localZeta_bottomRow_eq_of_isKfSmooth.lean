-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth
-- name    : AutomorphicForm.exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/3bd44bda-a94c-5b41-a43c-fe8b88158504
-- title:
--   Finite-adelic Godement sections realise K_f-smooth Borel-equivariant functions
-- statement:
--   Let $F$ be a number field, equipped at each finite place $v$ (a height-one prime $v$ of $\mathcal O_F$) with a measurable and Borel space structure on the completion $F_v$ and an additive Haar measure $\mu_{f,v}$; let $\mu,\nu\colon(\mathbb A_F)^\times\to\mathbb C^\times$ be characters whose underlying complex-valued functions are continuous. Let $n\in\mathbb N$ and let $U_0,\dots,U_{n-1}\colon \mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ satisfy: each $U_i$ is `IsKfSmooth`, i.e. a smooth vector for right translation by the kernel of `glArch` (the matrices with trivial archimedean component); and each $U_i$ transforms by $U_i(bg)=\mu(b_{00})\,\nu(b_{11})\,U_i(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (lower-left entry zero) with trivial archimedean part and integral finite part, $b_{00},b_{11}$ being the diagonal units attached to $b$. Then there is a finite set $S$ of finite places such that for $v\notin S$ both $\mu$ and $\nu$ are unramified at $v$ (their local components `localChar` are trivial on units of $F_v$ that are integral together with their inverses), together with integers $m_i$, functions $h_{i,j}\colon (\mathbb A_F^f)^2\to\mathbb C$ and local functions $\Phi_{i,j,v}\colon F_v^2\to\mathbb C$, for $j<m_i$, such that every $h_{i,j}$ is locally constant with compact support, vanishes at any $y$ having some coordinate non-integral at some $v\notin S$, and satisfies $h_{i,j}(y)=\prod_{v\in S}\Phi_{i,j,v}(y_v)$ whenever all coordinates of $y$ are integral outside $S$; and, for every $i$, every $z\in\mathbb C$ and every $k$ in `adelicMaximalCompact` with trivial archimedean component (so that its finite part is integral),
--   $$\sum_{j<m_i}\mu(\det k)\prod_{v\in S}Z_v\bigl(t\mapsto \Phi_{i,j,v}(t\cdot e_v(k)),\ (\mu\nu^{-1})_v,\ z\bigr)=U_i(k),$$
--   where $e_v(k)$ is the bottom row of the local component of the finite part of $k$ at $v$ and $Z_v$ is Tate's local zeta integral [`LanglandsTunnell.TateLocal.localZeta`](def/LanglandsTunnell_TateLocalZeta.html#L125) for the measure $\mu_{f,v}$.
--
--   This is the non-archimedean half of the assertion that Godement sections span the smooth induced representation of $\mathrm{GL}_2(\mathbb A_F^f)$ attached to the Borel character $(\mu,\nu)$: finitely many factorizable locally constant functions on $(\mathbb A_F^f)^2$, standard outside a finite set $S$ of places, reproduce prescribed $K_f$-smooth Borel-equivariant functions on the maximal compact subgroup through Tate local zeta integrals. It feeds the construction of partial Euler products for such families, being cited by [`AutomorphicForm.exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family`](thm.html#AutomorphicForm.exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth
    (F : Type) [Field F] [NumberField F]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (n : ℕ) (U : Fin n → AdelicGL2 (𝓞 F) F → ℂ)
    (_hUf : ∀ i, IsKfSmooth F (U i))
    (_hUB : ∀ (i : Fin n) (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
        glArch (𝓞 F) F b = 1 → glFin (𝓞 F) F b ∈ finiteIntegralGL2 (𝓞 F) F →
        ∀ g : AdelicGL2 (𝓞 F) F,
          U i (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U i g) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))),
      (∀ v ∉ S, IsUnramifiedCharAt μ v ∧ IsUnramifiedCharAt ν v) ∧
      ∃ (m : Fin n → ℕ)
        (h : (i : Fin n) → Fin (m i) → (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ)
        (Φf : (i : Fin n) → Fin (m i) → (v : HeightOneSpectrum (𝓞 F)) → (Fin 2 → v.adicCompletion F) → ℂ),
        (∀ i j, IsLocallyConstant (h i j)) ∧
        (∀ i j, HasCompactSupport (h i j)) ∧
        (∀ i j (y : Fin 2 → FiniteAdeleRing (𝓞 F) F),
          (∃ v ∉ S, ∃ l, y l v ∉ v.adicCompletionIntegers F) → h i j y = 0) ∧
        (∀ i j (y : Fin 2 → FiniteAdeleRing (𝓞 F) F),
          (∀ v ∉ S, ∀ l, y l v ∈ v.adicCompletionIntegers F) →
            h i j y = ∏ v ∈ S, Φf i j v (fun l => y l v)) ∧
        ∀ (i : Fin n) (z : ℂ) (k : AdelicGL2 (𝓞 F) F),
          k ∈ adelicMaximalCompact F → glArch (𝓞 F) F k = 1 →
            (∑ j, ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
                * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v)
                    (fun t => Φf i j v (fun l => t
                      * (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) :
                          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 l))
                    (localChar (μ * ν⁻¹) v) z)
              = U i k := by sorry
