-- Prove2me | Theorems.Thm_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell
-- name    : AutomorphicForm.exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/31764e1a-1ebc-5e18-b0d7-c7cfbb2d1097
-- title:
--   Log-linearity of norm-band covolumes for elliptic centralizer tori
-- statement:
--   Let $K$ be a number field and let $\gamma_0 \in \mathrm{GL}_2(K)$ be elliptic in the sense that the characteristic polynomial of the underlying matrix of $\gamma_0$ has no root in $K$. Let $u$ be a unit of the adele ring $\mathbb{A}_K$ of $K$, write $\gamma = \mathrm{globalPoints}(\gamma_0)\cdot \mathrm{centralScalar}(u)$ for the product in $\mathrm{GL}_2(\mathbb{A}_K)$ of the image of $\gamma_0$ under the map induced by $K \to \mathbb{A}_K$ with the scalar matrix $u\cdot 1$, and let $T = Z_{\mathrm{GL}_2(\mathbb{A}_K)}(\{\gamma\})$ be the centralizer of the singleton $\{\gamma\}$, equipped with its Borel $\sigma$-algebra (that of $\mathrm{GL}_2(\mathbb{A}_K)$ likewise being Borel) and with a Haar measure $\tau$. Then there is a constant $C \in [0,\infty]$ with $C \neq 0$ and $C \neq \infty$ such that for every subset $D \subseteq T$ which is a fundamental domain, with respect to $\tau$, for the right-translation action on $T$ of the subgroup obtained by pushing the centralizer of $\{\gamma_0\}$ in $\mathrm{GL}_2(K)$ forward to $\mathrm{GL}_2(\mathbb{A}_K)$ and viewing it inside $T$, and for all reals $a, b$ with $0 < a \le b$, one has $$\tau\bigl(D \cap \{t \in T : \|\det t\| \in [a,b]\}\bigr) = C\cdot \log(b/a),$$ where $\|x\|$ denotes the idelic norm of $x \in \mathbb{A}_K^\times$, defined as the value at $x$ of the distributive Haar character of $\mathbb{A}_K$, and the right-hand side is read in $[0,\infty]$.
--
--   This is Tate's computation of the Haar volume of a norm band in the idele class group, transported to the centralizer torus of an elliptic element of $\mathrm{GL}_2$: for elliptic $\gamma_0$ the algebra $K[\gamma_0]$ is a quadratic field $E$, the torus $T$ is $\mathbb{A}_E^\times$, the rational centralizer is $E^\times$, and $\|\det t\| = \|t\|_E$. It supplies the finiteness and log-linearity of elliptic covolumes used in the comparison of twisted orbital integrals with orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell
    (K : Type) [Field K] [NumberField K]
    (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K) (u : (AdeleRing (𝓞 K) K)ˣ)
    (τ : Measure (Subgroup.centralizer
      ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K u} :
        Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    [τ.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ D : Set (Subgroup.centralizer
        ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K u} :
          Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
        IsFundamentalDomain
          (((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map
            (AutomorphicForm.globalPoints (𝓞 K) K)).subgroupOf
            (Subgroup.centralizer {AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
              AutomorphicForm.centralScalar (𝓞 K) K u})).op D τ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) := by sorry
