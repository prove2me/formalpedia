-- Prove2me | Theorems.Thm_ContactTopology_global_invariant_collar_foliation_realization
-- name    : ContactTopology.global_invariant_collar_foliation_realization
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T19:28:49.499432+00:00
-- url     : https://prove2.me/theorems/41c2a5c3-9362-4e62-a595-632b26ce1e3f
-- title:
--   Foliation realization in a globally invariant contact collar
-- statement:
--   Let $u:\mathbb R^2\to\mathbb R$ and $\beta_0,\beta_1\in\Omega^1(\mathbb R^2)$ be smooth. Suppose the two invariant forms
--   $$
--   \alpha_i=\beta_i+u\,dz\qquad(i=0,1)
--   $$
--   are positive contact forms on $\mathbb R^2\times\mathbb R$, and $\beta_1=\beta_0$ outside a compact set $K\subset\mathbb R^2$. In coordinates $\beta=b_1\,dx+b_2\,dy$, positivity means
--   $$
--   Q(\beta)=b_1u_y-b_2u_x+u\bigl((b_2)_x-(b_1)_y\bigr)>0.
--   $$
--   Then there is a smooth ambient isotopy $H_t$ of $\mathbb R^3$, with a jointly smooth inverse family $G_t$, a compact set $C\subset\mathbb R^3$ outside which $H_t$ is the identity, and jointly smooth positive functions $\sigma_t$, such that $H_0=\mathrm{id}$ and
--   $$
--   H_1^*\alpha_0=\sigma_1\alpha_1\qquad\text{on }\mathbb R^2\times[-1,1].
--   $$
--   For every point $(x,y,z)$ with $u(x,y)=0$, both $H_t$ and $G_t$ keep the horizontal coordinates $(x,y)$ fixed. These families extend smoothly to all real times.
--
--   Thus $H_1$ embeds the invariant unit collar for $\alpha_1$ into the original contact space $(\mathbb R^3,\ker\alpha_0)$. Its central plane has the characteristic foliation prescribed by $\ker\beta_1$, with the dividing locus tracked by $u=0$.
--
--   This statement concerns a **globally invariant product model**. It gives no prescribed bound on the size of $C$ or on the image of the collar. In particular, it is not a realization theorem inside an arbitrarily small given neighborhood, and it does not establish bypass existence or tight-solid-torus classification.
-- source:
--   Coordinate consequence of the Moser argument in Hansjorg Geiges, Contact Geometry, https://arxiv.org/abs/math/0307242 (v2), Section 2.2, Lemma 2.19 and proof of Theorem 2.20. Invariant convex-surface collars beta+u dt are reviewed by Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/abs/2207.03590v2, Section 2.2, proof of Lemma 2.7. The cutoff construction, global-product specialization and two-sided dividing-fibre tracking are the present coordinate argument; the sources are not asserted to state this exact global model theorem or the support-size conclusion.

import Mathlib
open Set Function
open scoped ContDiff

theorem ContactTopology.global_invariant_collar_foliation_realization
    (u : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K)
    (heq : ∀ x, x ∉ K → β₁ x = β₀ x) :
    let Q : (((Fin 2 → ℝ) → (Fin 2 → ℝ))) → (Fin 2 → ℝ) → ℝ := fun β x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    let I : (((Fin 2 → ℝ) → (Fin 2 → ℝ))) → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
      fun β y => ![β ![y 0,y 1] 0,β ![y 0,y 1] 1,u ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    (∀ x, 0 < Q β₀ x) → (∀ x, 0 < Q β₁ x) →
    ∃ H G : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ σ : ℝ → (Fin 3 → ℝ) → ℝ,
      ∃ C : Set (Fin 3 → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => G p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => σ p.1 p.2) ∧
      IsCompact C ∧ (∀ y, H 0 y = y) ∧
      (∀ t y, H t (G t y) = y) ∧ (∀ t y, G t (H t y) = y) ∧
      (∀ t y, y ∉ C → H t y = y) ∧ (∀ t y, 0 < σ t y) ∧
      (∀ t y, u ![y 0,y 1] = 0 →
        (H t y 0 = y 0 ∧ H t y 1 = y 1) ∧ (G t y 0 = y 0 ∧ G t y 1 = y 1)) ∧
      ∀ y, |y 2| ≤ 1 → ∀ v,
        B (I β₀ (H 1 y)) (fderiv ℝ (H 1) y v) = σ 1 y*B (I β₁ y) v := by sorry
