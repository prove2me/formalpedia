-- Prove2me | Theorems.Thm_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported
-- name    : AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/a050dded-515e-5886-a607-64dede7055ba
-- title:
--   Uniform approximation of band-supported invariant functions by elementary tensors
-- statement:
--   Let $F$ be a number field, and let $a',b',a_1,b_1$ be reals with $0<a'$, $a'<a_1$ and $b_1<b'$. Write $\mathbf K=$ `adelicMaximalCompact F` for the subgroup of $\mathrm{GL}_2(\mathbb A_F)$ consisting of those $k$ whose finite component lies in `finiteIntegralGL2` and whose component at each infinite place $w$ is a row isometry (determinant of absolute value $1$, and the associated map on row vectors preserving $\|x\|^2+\|y\|^2$). Let $G:\mathbb A_F^\times\times\mathbf K\to\mathbb C$ be continuous, invariant under left translation of the first variable by the principal ideles (the image of $F^\times$ under `Units.map` of $F\to\mathbb A_F$), and such that $G(t,k)\neq 0$ forces $\|t\|\in[a_1,b_1]$, where $\|t\|$ is the idele norm, namely the value at $t$ of the distributive Haar character of $\mathbb A_F$. Then for every $\varepsilon>0$ there are $n\in\mathbb N$ and families $\mu_j:\mathbb A_F^\times\to\mathbb C^\times$, $h_j:\mathbb R\to\mathbb C$, $m_j:\mathbf K\to\mathbb C$ indexed by $j\in\mathrm{Fin}\,n$ such that: each $\mu_j$ is a group homomorphism with $|\mu_j(x)|=1$ for all $x$, trivial on the image of $F^\times$, and continuous as a $\mathbb C$-valued function; each $h_j$ is $C^\infty$ on $\mathbb R$, compactly supported, and vanishes outside $[\log a',\log b']$; each $m_j$ is continuous, right $\mathbf K$-finite in the sense that all right translates $k\mapsto m_j(kk_0)$ lie in one finite-dimensional $\mathbb C$-subspace of functions $\mathbf K\to\mathbb C$, and right invariant under the elements $u$ of $\mathbf K$ lying in some neighbourhood $V$ of $1$ in $\mathrm{GL}_2(\mathbb A_F)$ and in the kernel of the archimedean projection `glArch`; and finally $$\Bigl\|G(t,k)-\sum_{j}\mu_j(t)\,h_j(\log\|t\|)\,m_j(k)\Bigr\|\le\varepsilon$$ for all $(t,k)\in\mathbb A_F^\times\times\mathbf K$.
--
--   This is the uniform (sup-norm) approximation step for functions on the idele class group times the maximal compact subgroup: a continuous function supported in a norm band $[a_1,b_1]$ is approximated, to within $\varepsilon$ everywhere, by a finite sum of elementary tensors built from unitary idele class characters, smooth functions of $\log\|t\|$ supported in the slightly larger band $[\log a',\log b']$, and $\mathbf K$-finite, locally constant-in-the-finite-direction functions on $\mathbf K$. It is used to obtain the corresponding $L^p$-type approximation statement [`AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_continuous_invariant_bandSupported`](thm.html#AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_continuous_invariant_bandSupported).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.lean

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported
    (F : Type) [Field F] [NumberField F]
    (a' b' a₁ b₁ : ℝ) (ha' : 0 < a') (ha₁ : a' < a₁) (hb₁ : b₁ < b')
    (G : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ) (hGc : Continuous G)
    (hGinv : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G (γ * p.1, p.2) = G p)
    (hGsupp : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G p ≠ 0 → NumberField.TateGlobal.ideleNorm F p.1 ∈ Set.Icc a₁ b₁)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (μ : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (h : Fin n → ℝ → ℂ)
      (m : Fin n → ↥(adelicMaximalCompact F) → ℂ),
      (∀ j, IsUnitaryChar (𝓞 F) F (μ j)) ∧ (∀ j, IsIdeleClassChar (𝓞 F) F (μ j)) ∧
      (∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ j x : ℂˣ) : ℂ)) ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (h j)) ∧ (∀ j, HasCompactSupport (h j)) ∧
      (∀ (j : Fin n) (u : ℝ), h j u ≠ 0 → u ∈ Set.Icc (Real.log a') (Real.log b')) ∧
      (∀ j, Continuous (m j)) ∧
      (∀ j, ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
        ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => m j (k * k₀)) ∈ W) ∧
      (∀ j, ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u : ↥(adelicMaximalCompact F)),
        (u : AdelicGL2 (𝓞 F) F) ∈ V → (u : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F →
          m j (k * u) = m j k) ∧
      ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), ‖G p - ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2‖ ≤ ε := by sorry
