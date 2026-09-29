-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lintegral_localCentralizer_eq_mul_lintegral_prod_norm_inv_of_not_isSquare
-- name    : AutomorphicForm.exists_forall_lintegral_localCentralizer_eq_mul_lintegral_prod_norm_inv_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/0c5294a2-ee3b-55ee-b07e-f84f6a1c35c7
-- title:
--   Haar measure on an elliptic torus in (p,r)-coordinates
-- statement:
--   Let $K$ be a number field and $v$ a nonzero prime of its ring of integers, and let $F = K_v$ be the $v$-adic completion, equipped with a measurable structure that is the Borel structure of its topology and with an additive Haar measure $\mu$. Let $d \in F$ be an element that is not a square, let $p_0, r_0 \in F$ with $r_0 \neq 0$, and let $u \in \mathrm{GL}_2(F)$ be an element whose underlying matrix is $\begin{pmatrix} p_0 & r_0 \\ d r_0 & p_0\end{pmatrix}$. Let $\tau$ be a Haar measure on the subgroup $\mathrm{Subgroup.centralizer}\,\{u\}$ of $\mathrm{GL}_2(F)$, taken with the Borel structure of its subspace topology. Then there is a constant $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$ such that for every function $H \colon \mathrm{GL}_2(F) \to [0,\infty]$ measurable for the Borel structure on $\mathrm{GL}_2(F)$,
--   $$\int_{t \in \mathrm{centralizer}(u)} H(t)\, d\tau = c \int_{(p,r) \in F \times F} H\Bigl(\begin{pmatrix} p & r \\ d r & p \end{pmatrix}\Bigr)\, \|p^2 - d r^2\|^{-1}\, d(\mu \times \mu),$$
--   where the integrand on the right is interpreted as $0$ at those $(p,r)$ for which $\det \begin{pmatrix} p & r \\ d r & p\end{pmatrix} = 0$, and otherwise the matrix is regarded as an element of $\mathrm{GL}_2(F)$ via its nonvanishing determinant. The constant $c$ depends only on $K$, $v$, $\mu$, $d$, $u$ and $\tau$, not on $H$; the integrals are Lebesgue integrals of $[0,\infty]$-valued functions.
--
--   This is the local statement that the multiplicative Haar measure of the quadratic extension $E = F(\sqrt d)$, viewed through the regular representation as the centralizer torus of the regular elliptic element $u$ in $\mathrm{GL}_2(F)$, is a constant multiple of $\|N_{E/F}\|^{-1}$ times additive Haar measure in the coordinates $(p,r) \mapsto p + r\sqrt d$. It is used to evaluate orbital integrals at elliptic elements in explicit coordinates, and is cited in that form by [`AutomorphicForm.exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare`](thm.html#AutomorphicForm.exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lintegral_localCentralizer_eq_mul_lintegral_prod_norm_inv_of_not_isSquare.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

theorem AutomorphicForm.exists_forall_lintegral_localCentralizer_eq_mul_lintegral_prod_norm_inv_of_not_isSquare
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (d : v.adicCompletion K) (hd : ¬ IsSquare d) (p₀ r₀ : v.adicCompletion K) (hr₀ : r₀ ≠ 0)
    (u : GL (Fin 2) (v.adicCompletion K))
    (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![p₀, r₀; d * r₀, p₀])
    (τ : @Measure (AutomorphicForm.localCentralizer K v u) (AutomorphicForm.localCentralizerBorel K v u))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v u) τ) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ H : GL (Fin 2) (v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.localGLBorel K v] H →
        (letI := AutomorphicForm.localCentralizerBorel K v u
         ∫⁻ t, H (t : GL (Fin 2) (v.adicCompletion K)) ∂τ) =
          c * ∫⁻ q : v.adicCompletion K × v.adicCompletion K,
            (if h : (!![q.1, q.2; d * q.2, q.1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
                H (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) *
              ENNReal.ofReal ‖q.1 ^ 2 - d * q.2 ^ 2‖⁻¹ ∂(μ.prod μ) := by sorry
