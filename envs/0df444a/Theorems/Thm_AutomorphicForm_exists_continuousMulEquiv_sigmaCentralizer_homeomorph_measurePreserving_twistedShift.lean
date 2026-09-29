-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift
-- name    : AutomorphicForm.exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/b682bbae-77a0-5854-868f-5b630644b9b3
-- title:
--   Straightening a θ-twisted cyclic shift on G^{m+1}
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, second countable, and equipped with its Borel $\sigma$-algebra; let $\theta \colon G \to G$ be a group homomorphism (no continuity or measurability of $\theta$ is assumed), let $m$ be a natural number, $\delta = (\delta_0,\dots,\delta_m) \in G^{m+1}$, and let $\mu$ be a $\sigma$-finite left-invariant measure on $G$. Write $\rho$ for the endomorphism of $G^{m+1}$ whose $k$-th component for $k<m+1$ sending $x$ to $x_{k+1}$ and whose last component sends $x$ to $\theta(x_0)$, i.e. $\rho(x_0,\dots,x_m) = (x_1,\dots,x_m,\theta(x_0))$; write $\nu = \delta_0\delta_1\cdots\delta_m$ for the ordered product of the entries of $\delta$. For a homomorphism $\sigma$ and an element $d$, [`AutomorphicForm.sigmaCentralizer`](def/AutomorphicForm_SigmaCentralizer.html#L10) $\sigma\, d$ is the subgroup $\{t : t\,d\,(\sigma t)^{-1} = d\}$. The assertion is the existence of an isomorphism of topological groups $e$ from the $\rho$-twisted centralizer of $\delta$ in $G^{m+1}$ onto the $\theta$-twisted centralizer of $\nu$ in $G$, and of a homeomorphism $X \colon G \times G^{m} \to G^{m+1}$, such that: the element of $G$ underlying $e(t)$ is $t_0$; $X$ pushes $\mu \otimes \mu^{\otimes m}$ forward to $\mu^{\otimes (m+1)}$; $X(x_0,u)_0 = x_0$; for all $(x_0,u)$,
--   $$X(x_0,u)^{-1}\,\delta\,\rho\big(X(x_0,u)\big) = \big(u_0,\dots,u_{m-1},\,(u_0\cdots u_{m-1})^{-1}\,x_0^{-1}\,\nu\,\theta(x_0)\big);$$
--   and $t \cdot X(x_0,u) = X\big(e(t)\,x_0,\,u\big)$ for every $t$ in the $\rho$-twisted centralizer of $\delta$.
--
--   This is the change of variables underlying the reduction of a twisted orbital integral over a product of $m+1$ copies of $G$, cyclically permuted with the wrap-around factor twisted by $\theta$, to a $\theta$-twisted orbital integral over a single copy of $G$: the twisted conjugate acquires $m$ free coordinates and one coordinate $x_0^{-1}\nu\,\theta(x_0)$, the twisted centralizer acts only through its image in $G$, and the measure is unchanged. It is used by [`AutomorphicForm.exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one`](thm.html#AutomorphicForm.exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift.lean

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (θ : G →* G) {m : ℕ} (δ : Fin (m + 1) → G)
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] :
    ∃ (e : AutomorphicForm.sigmaCentralizer
            (MonoidHom.pi fun j : Fin (m + 1) =>
              Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ ≃ₜ*
          AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod)
      (X : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G)),
      (∀ t, ((e t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod) : G) =
        (t : Fin (m + 1) → G) 0) ∧
      MeasurePreserving X (μ.prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) ∧
      (∀ p : G × (Fin m → G), X p 0 = p.1) ∧
      (∀ p : G × (Fin m → G),
        (X p)⁻¹ * δ *
            (MonoidHom.pi fun j : Fin (m + 1) =>
              Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) (X p) =
          Fin.snoc p.2 (((List.ofFn p.2).prod)⁻¹ * (p.1⁻¹ * (List.ofFn δ).prod * θ p.1))) ∧
      (∀ (t : AutomorphicForm.sigmaCentralizer
              (MonoidHom.pi fun j : Fin (m + 1) =>
                Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                  (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                  (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ)
          (p : G × (Fin m → G)),
        (t : Fin (m + 1) → G) * X p =
          X (((e t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod) : G) * p.1, p.2)) := by sorry
