-- Prove2me | Theorems.Thm_CircleDesign_hopfield_threshold_circle_three_design
-- name    : CircleDesign.hopfield_threshold_circle_three_design
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T05:36:12.238215+00:00
-- url     : https://prove2.me/theorems/59f640be-2054-406a-bccf-157f68588339
-- title:
--   Weighted Hopfield energy of a unit-circle bank in $\mathbb{R}^2$ is globally convex exactly for $0<\beta\le 2$, with $\beta=2$ attained iff the third moments vanish
-- statement:
--   ## Setting
--
--   Fix a **finite weighted memory bank on the unit circle** in the plane: a finite index set $I$, vectors $m_i \in \mathbb{R}^2$ with $\|m_i\| = 1$, and strictly positive weights $w_i > 0$. Assume the bank is **centered** and **isotropic**:
--
--   $$\sum_{i \in I} w_i\, m_i = 0, \qquad \sum_{i \in I} w_i \langle m_i, v\rangle^2 = \frac{\|v\|^2}{2} \quad \text{for every } v \in \mathbb{R}^2 .$$
--
--   The second condition is the matrix statement $\sum_i w_i m_i m_i^{\top} = I/2$. Combined with $\|m_i\| = 1$ it forces $\sum_i w_i = 1$, so such a bank is exactly a centered isotropic probability measure supported on the unit circle.
--
--   Say the bank has **vanishing third moments** if
--
--   $$\sum_{i \in I} w_i \langle m_i, v\rangle^3 = 0 \qquad \text{for every } v \in \mathbb{R}^2 ,$$
--
--   which by polarization is equivalent to the vanishing of every entry $\sum_i w_i (m_i)_a (m_i)_b (m_i)_c$ of the symmetric third-moment tensor. Together with centering and isotropy this says precisely that the bank is a probabilistic **spherical $3$-design** on the circle.
--
--   For a real parameter $\beta$, the associated **weighted (dense associative) Hopfield energy** is
--
--   $$E_\beta(u) \;=\; \frac{\|u\|^2}{2} \;-\; \frac{1}{\beta}\,\log \sum_{i \in I} w_i\, e^{\beta \langle m_i, u\rangle}, \qquad u \in \mathbb{R}^2 .$$
--
--   ## Statement
--
--   Let the bank be finite, with positive weights, unit-norm vectors in $\mathbb{R}^2$, centered and isotropic as above. Then:
--
--   1. **$\beta = 2$ is the largest possible threshold.** For every $\beta > 2$, the function $E_\beta$ is *not* convex on $\mathbb{R}^2$.
--
--   2. **Attaining the threshold characterizes $3$-designs.** $E_2$ is convex on all of $\mathbb{R}^2$ if and only if the bank has vanishing third moments.
--
--   3. **A $3$-design is convex on the whole admissible range.** If the third moments vanish, then $E_\beta$ is convex on $\mathbb{R}^2$ for every $\beta$ with $0 < \beta \le 2$.
--
--   4. **Strong convexity strictly below the threshold.** If the third moments vanish, then for every $\beta$ with $0 < \beta < 2$ there is a constant $c > 0$ such that $E_\beta$ is $c$-strongly convex on $\mathbb{R}^2$.
--
--   Items 1 and 3 together say that for a finite unit-circle $3$-design bank with prescribed positive weights, $E_\beta$ is globally convex *exactly* for $0 < \beta \le 2$; item 4 adds that it is strongly convex for $0 < \beta < 2$. Item 2 is the exact-characterization half: among centered isotropic unit-circle banks, attaining the largest possible threshold $\beta = 2$ is equivalent to the vanishing of the third moments.
--
--   ## Role
--
--   The Hessian of $E_\beta$ at $u$ is $I - \beta\,\mathrm{Cov}_{\mu_{\beta u}}(X)$, where $\mu_\theta$ is the exponential tilt of the bank $\mu = \sum_i w_i \delta_{m_i}$ by $\theta$. The statement is therefore the Hopfield translation of the sharp covariance bound $\mathrm{Cov}_{\mu_\theta}(X) \preceq I/2$ for all tilts $\theta \in \mathbb{R}^2$, and of its converse: that bound holds precisely for the centered isotropic circle laws whose third-moment tensor vanishes. Necessity of $\beta \le 2$ is read off at the origin, where the Hessian equals $(1 - \beta/2) I$.
--
--   ## What is *not* claimed
--
--   The result is two-dimensional and equal-radius. **No higher-dimensional analogue is asserted**, and the restriction is essential: the uniform law on $\{\pm e_1, \pm e_2, \pm e_3\} \subset \mathbb{R}^3$ is a spherical $3$-design with covariance $I_3/3$, yet tilting by $\theta = (\log 4, \log 4, 0)$ gives variance $17/42 > 1/3$ in the direction $(1,-1,0)/\sqrt{2}$, so vanishing third moments does not suffice for the corresponding covariance domination in dimension three. No unequal-radius extension is asserted either. Finiteness of the bank, strict positivity of every weight, and unit norms are all hypotheses of the statement. Nothing is claimed for $\beta \le 0$.
--
--   **Formalization Note.** The plane is `EuclideanSpace ℝ (Fin 2)`, and the bank is a `Fintype`-indexed family `m : ι → EuclideanSpace ℝ (Fin 2)` with weights `w : ι → ℝ`. Isotropy and the third-moment condition are stated in their equivalent scalar (quadratic- and cubic-form) versions, which over $\mathbb{R}$ determine the symmetric moment tensors by polarization. The energy is introduced as a function variable `E` pinned by a defining hypothesis `hE`, so that no auxiliary `def` is needed. Convexity is `ConvexOn ℝ Set.univ`; strong convexity is Mathlib's `StrongConvexOn Set.univ c`, which for modulus $c$ means $u \mapsto E_\beta(u) - \tfrac{c}{2}\|u\|^2$ is convex. Only the existence of a positive modulus is asserted, matching the source's unquantified phrase "strongly convex".
-- source:
--   reports/odd_circle_global.md, "Consequences and scope" section, bullet "Weighted Hopfield energies" (line 254) together with the scope paragraph (line 257) and the dimension-three counterexample (lines 259-264); main theorem in the "The theorem" section (lines 7-35), dated 2026-09-19. Same corollary previously recorded in reports/isotropic_circle_analytic.md, "Consequences and scope", item 2 (lines 170-176). Independently audited in reports/odd_circle_global_audit.md, section 5 "Equality and consequences" (line 67).

import Mathlib

open scoped InnerProductSpace

namespace CircleDesign

theorem hopfield_threshold_circle_three_design
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (m : ι → EuclideanSpace ℝ (Fin 2))
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hw : ∀ i, 0 < w i)
    (hunit : ∀ i, ‖m i‖ = 1)
    (hcentered : ∑ i, w i • m i = 0)
    (hisotropic : ∀ v : EuclideanSpace ℝ (Fin 2),
      ∑ i, w i * ⟪m i, v⟫_ℝ ^ 2 = ‖v‖ ^ 2 / 2)
    (hE : ∀ (β : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      E β u = ‖u‖ ^ 2 / 2 -
        β⁻¹ * Real.log (∑ i, w i * Real.exp (β * ⟪m i, u⟫_ℝ))) :
    (∀ β : ℝ, 2 < β →
        ¬ ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) (E β)) ∧
    (ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) (E 2) ↔
        ∀ v : EuclideanSpace ℝ (Fin 2), ∑ i, w i * ⟪m i, v⟫_ℝ ^ 3 = 0) ∧
    ((∀ v : EuclideanSpace ℝ (Fin 2), ∑ i, w i * ⟪m i, v⟫_ℝ ^ 3 = 0) →
      (∀ β : ℝ, 0 < β → β ≤ 2 →
          ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) (E β)) ∧
      (∀ β : ℝ, 0 < β → β < 2 →
          ∃ c : ℝ, 0 < c ∧
            StrongConvexOn (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) c (E β))) := by sorry

end CircleDesign
