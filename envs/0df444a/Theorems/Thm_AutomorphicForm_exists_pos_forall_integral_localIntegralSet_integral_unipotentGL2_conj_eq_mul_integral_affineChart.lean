-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_localIntegralSet_integral_unipotentGL2_conj_eq_mul_integral_affineChart
-- name    : AutomorphicForm.exists_pos_forall_integral_localIntegralSet_integral_unipotentGL2_conj_eq_mul_integral_affineChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/539c8838-7594-55e0-9498-908b2d254898
-- title:
--   Unipotent orbital integral: Iwasawa versus affine-chart normalisation
-- statement:
--   Let $K$ be a number field and $v$ a nonzero prime of its ring of integers, with completion $K_v =$ `v.adicCompletion K` and valuation ring $\mathcal{O}_v$. Let $\sigma : K_v \times K_v^{\times} \to \mathrm{GL}_2(K_v)$ be a map whose underlying matrix is $\sigma(a,b) = \begin{pmatrix} 1 & 0 \\ a & b\end{pmatrix}$ for all $a \in K_v$, $b \in K_v^{\times}$. Equip $K_v$ with a measurable structure that is the Borel structure of its topology and with an additive Haar measure $\mu$, and $K_v^{\times}$ likewise with a Borel structure and a (multiplicative) Haar measure $\nu$. Then there is a real constant $c_0 > 0$ such that for every $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ that is locally constant and has compact support, one has, with $\mathrm{GL}_2(K_v)$ carrying the Borel structure of its topology,
--   $$\int_{\mathrm{GL}_2(K_v)} \mathbf{1}_{S}(k)\Bigl(\int_{K_v} f_v\bigl(k^{-1} n(x) k\bigr)\, d\mu(x)\Bigr) d\lambda(k) \;=\; c_0 \int_{K_v^{\times} \times K_v} f_v\bigl(\sigma(a,b)^{-1} n(1) \sigma(a,b)\bigr)\, d(\nu \otimes \mu)(b,a),$$
--   where $n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ is [`AutomorphicForm.unipotentGL2`](def/AutomorphicForm_ConstantTerm.html#L17), $S$ is the set of $g \in \mathrm{GL}_2(K_v)$ such that both $g$ and $g^{-1}$ have all entries in $\mathcal{O}_v$, and $\lambda$ is the Haar measure [`AutomorphicForm.localHaar`](def/AutomorphicForm_LocalOrbitalBase.html#L168) of $\mathrm{GL}_2(K_v)$ normalised so that the compact set $S$, viewed as a positive compact, has measure one. The constant $c_0$ is independent of $f_v$.
--
--   This is the comparison of the two standard normalisations of the regular unipotent orbital integral on $\mathrm{GL}_2$ over a nonarchimedean local field: on one side the orbit is swept out in the Iwasawa form $k^{-1}n(x)k$ with $k$ integral, on the other by the affine chart $\sigma(a,b)$ transverse to the centraliser of $n(1)$, and the two differ by a positive factor depending only on the chosen Haar measures. It feeds the local analysis of orbital integrals at elements of the local centralizer used in [`AutomorphicForm.exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare`](thm.html#AutomorphicForm.exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_integral_localIntegralSet_integral_unipotentGL2_conj_eq_mul_integral_affineChart.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_pos_forall_integral_localIntegralSet_integral_unipotentGL2_conj_eq_mul_integral_affineChart
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (σ : v.adicCompletion K → (v.adicCompletion K)ˣ → GL (Fin 2) (v.adicCompletion K))
    (hσ : ∀ (a : v.adicCompletion K) (b : (v.adicCompletion K)ˣ),
      (σ a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![1, 0; a, (b : v.adicCompletion K)])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
    (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure] :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, AutomorphicForm.IsLocalTestFn K v fv →
        (letI := AutomorphicForm.localGLBorel K v
          ∫ k, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
            (∫ x, fv (k⁻¹ * AutomorphicForm.unipotentGL2 x * k) ∂μ) ∂(AutomorphicForm.localHaar K v)) =
        (c₀ : ℂ) * ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
            fv ((σ q.2 q.1)⁻¹ * AutomorphicForm.unipotentGL2 1 * σ q.2 q.1) ∂(ν.prod μ) := by sorry
