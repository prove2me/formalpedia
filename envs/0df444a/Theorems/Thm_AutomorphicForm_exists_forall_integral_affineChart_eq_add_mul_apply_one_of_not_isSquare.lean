-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
-- name    : AutomorphicForm.exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/a3497c06-6398-51ff-9b2c-5dbae5187f5b
-- title:
--   Shalika germ expansion at the identity for GL₂
-- statement:
--   Let $K$ be a number field and $v$ a finite place of $K$, given by a maximal ideal of $\mathcal{O}_K$; write $K_v$ for the associated completion, equipped with a measurable structure that is the Borel structure of its topology, and let $\mu$ be an additive Haar measure on $K_v$ and $\nu$ a Haar measure on the unit group $K_v^{\times}$ (again with the Borel structure). Let $\delta, B$ be real numbers with $\delta > 0$. The assertion is that there exists $\varepsilon > 0$ such that for every $t \in K_v$ with $\|t\| < \varepsilon$ which is not a square in $K_v$ (so in particular $t \neq 0$), there is a nonzero complex number $\alpha$ with the following property: for every function $\Phi$ from the $2 \times 2$ matrices over $K_v$ to $\mathbb{C}$ such that (i) $\Phi(M + E) = \Phi(M)$ whenever all entries of $E$ have norm $\le \delta$, and (ii) $\Phi(M) \neq 0$ forces all entries of $M$ to have norm $\le B$, and for every function $J : K_v \to \mathbb{C}$ satisfying, for all $s \in K_v$,
--   $$J(s) = \int_{K_v^{\times} \times K_v} \Phi\left(1 + \begin{pmatrix} a & b \\ (s - a^2)/b & -a\end{pmatrix}\right)\, d(\nu \otimes \mu)(b, a),$$
--   one has $J(t) = J(0) + \alpha\,\Phi(1)$. Thus $\varepsilon$ depends only on $\delta$, $B$ and the chosen data $K, v, \mu, \nu$, and $\alpha$ depends on $t$ but is uniform in $\Phi$.
--
--   In the affine coordinates $(b,a) \mapsto 1 + \begin{pmatrix} a & b \\ (t-a^2)/b & -a\end{pmatrix}$, the integral parametrises the orbital integral of $\Phi$ over the conjugacy class of a regular element with characteristic polynomial determined by $t$, elliptic for $t$ a non-square and regular unipotent for $t = 0$; the conclusion is the two-term Shalika germ expansion $O_\gamma(\Phi) = O_{\mathrm{unip}}(\Phi) + \alpha\,\Phi(1)$ near the identity of $\mathrm{GL}_2(K_v)$, with the germ $\alpha$ nonzero and independent of the test function. It feeds the combined statement [`AutomorphicForm.exists_forall_sq_mul_eq_norm_mul_and_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare`](thm.html#AutomorphicForm.exists_forall_sq_mul_eq_norm_mul_and_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare), where the germ is compared with a normalising factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
    (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]
    (δ B : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion K, ‖t‖ < ε → ¬ IsSquare t →
      ∃ α : ℂ, α ≠ 0 ∧
        ∀ Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ,
          (∀ M E : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, ‖E i j‖ ≤ δ) → Φ (M + E) = Φ M) →
          (∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), Φ M ≠ 0 → ∀ i j, ‖M i j‖ ≤ B) →
          ∀ J : v.adicCompletion K → ℂ,
            (∀ s : v.adicCompletion K, J s = ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
              Φ (1 + !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
                (s - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) ∂(ν.prod μ)) →
            J t = J 0 + α * Φ 1 := by sorry
