-- Prove2me | Theorems.Thm_AutomorphicForm_exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one
-- name    : AutomorphicForm.exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/37b30a35-563b-56be-b20b-da8cde7818df
-- title:
--   Descent of twisted orbital integrals along the twisted shift
-- statement:
--   Let $G$ be a second countable, locally compact topological group carrying its Borel $\sigma$-algebra, let $\theta\colon G\to G$ be a continuous group endomorphism, let $m\in\mathbb N$ and $\delta=(\delta_0,\dots,\delta_m)\in G^{m+1}$. Write $\rho$ for the endomorphism of $G^{m+1}$ sending $(x_0,\dots,x_m)$ to $(x_1,\dots,x_m,\theta(x_0))$ (built from the evaluation maps by `Fin.lastCases`), and for a monoid endomorphism $\sigma$ and an element $\gamma$ let [`AutomorphicForm.sigmaCentralizer`](def/AutomorphicForm_SigmaCentralizer.html#L10) $\sigma\,\gamma$ denote the subgroup $\{t: t\gamma\sigma(t)^{-1}=\gamma\}$. Put $T=\{t\in G^{m+1}: t\delta\rho(t)^{-1}=\delta\}$ and $T_0=\{t_0\in G: t_0\nu\theta(t_0)^{-1}=\nu\}$, where $\nu=\delta_0\delta_1\cdots\delta_m$ is the ordered product `(List.ofFn δ).prod`. Let $\mu$ be a Haar measure on $G$, let $U\le G$ be an open subgroup with $\mu(U)=1$, let $\tau$ be an s-finite measure on $T$, and let $w\colon G^{m+1}\to\mathbb R$ be non-negative, measurable and compactly supported, satisfying $\int_T w(tx)\,d\tau(t)=1$ for every $x\in G^{m+1}$ with $x^{-1}\delta\rho(x)$ lying in $U^{m+1}$ (the product set $\prod_{j}U$). Then there exist an isomorphism of topological groups $e\colon T\to T_0$ and a function $s\colon G\to\mathbb R$ such that: $e(t)$ is the $0$-th coordinate $t_0$ of $t$ for all $t\in T$; $s$ is non-negative, measurable and compactly supported; $\int_{T_0}s(t x_0)\,d(e_*\tau)(t)=1$ for every $x_0\in G$ with $x_0^{-1}\nu\theta(x_0)\in U$; and, provided $x\mapsto \mathbf 1_{U^{m+1}}\!\big(x^{-1}\delta\rho(x)\big)\,w(x)$ (with values in $\mathbb C$) is integrable for the product measure $\mu^{\otimes(m+1)}$, one has $$\int_{G^{m+1}}\mathbf 1_{U^{m+1}}\!\big(x^{-1}\delta\rho(x)\big)\,w(x)\,d\mu^{\otimes(m+1)}(x)=\int_G\mathbf 1_{U}\!\big(x_0^{-1}\nu\theta(x_0)\big)\,s(x_0)\,d\mu(x_0).$$
--
--   This is the descent step identifying a $\rho$-twisted orbital integral of the unit $\mathbf 1_{U^{m+1}}$ at $\delta$ on $G^{m+1}$, computed through a section function relative to a measure $\tau$ on the $\rho$-twisted centraliser, with a $\theta$-twisted orbital integral of $\mathbf 1_U$ at the ordered product $\nu=\delta_0\cdots\delta_m$, computed through a section function relative to the transported measure on the $\theta$-twisted centraliser of $\nu$; it rests on the isomorphism and measure-preserving change of variables provided by [`AutomorphicForm.exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift`](thm.html#AutomorphicForm.exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift). It is used in the construction of Haar measures and local integral sets for twisted conjugation, the group-theoretic underpinning of the base-change comparison of orbital integrals for a cyclic extension, where $G=\mathrm{GL}_2$ of a local field and $U$ is its maximal compact subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one.lean

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (θ : G →* G) (hθ : Continuous θ) {m : ℕ} (δ : Fin (m + 1) → G)
    (μ : Measure G) [μ.IsHaarMeasure]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hμU : μ U = 1)
    (τ : Measure (AutomorphicForm.sigmaCentralizer
        (MonoidHom.pi fun j : Fin (m + 1) =>
          Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
            (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
            (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ)) [SFinite τ]
    (w : (Fin (m + 1) → G) → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hwc : HasCompactSupport w)
    (hsec : ∀ x : Fin (m + 1) → G,
      x⁻¹ * δ *
          (MonoidHom.pi fun j : Fin (m + 1) =>
            Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
              (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
              (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) x ∈
        Set.univ.pi (fun _ : Fin (m + 1) => (U : Set G)) →
      ∫ t : AutomorphicForm.sigmaCentralizer
          (MonoidHom.pi fun j : Fin (m + 1) =>
            Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
              (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
              (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ,
        w ((t : Fin (m + 1) → G) * x) ∂τ = 1) :
    ∃ (e : AutomorphicForm.sigmaCentralizer
            (MonoidHom.pi fun j : Fin (m + 1) =>
              Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ ≃ₜ*
          AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod)
      (s : G → ℝ),
      (∀ t, ((e t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod) : G) = (t : Fin (m + 1) → G) 0) ∧
      (∀ x, 0 ≤ s x) ∧ Measurable s ∧ HasCompactSupport s ∧
      (∀ x₀ : G, x₀⁻¹ * (List.ofFn δ).prod * θ x₀ ∈ U →
        ∫ t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod, s ((t : G) * x₀) ∂(Measure.map e τ) = 1) ∧
      (Integrable (fun x : Fin (m + 1) → G =>
          (Set.univ.pi fun _ : Fin (m + 1) => (U : Set G)).indicator (fun _ => (1 : ℂ))
            (x⁻¹ * δ *
              (MonoidHom.pi fun j : Fin (m + 1) =>
                Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                  (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                  (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) x) *
            (w x : ℂ)) (Measure.pi fun _ => μ) →
        ∫ x : Fin (m + 1) → G,
            (Set.univ.pi fun _ : Fin (m + 1) => (U : Set G)).indicator (fun _ => (1 : ℂ))
              (x⁻¹ * δ *
                (MonoidHom.pi fun j : Fin (m + 1) =>
                  Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                    (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                    (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) x) *
              (w x : ℂ) ∂(Measure.pi fun _ => μ) =
          ∫ x₀ : G, (U : Set G).indicator (fun _ => (1 : ℂ)) (x₀⁻¹ * (List.ofFn δ).prod * θ x₀) * (s x₀ : ℂ) ∂μ) := by sorry
