-- Prove2me | Theorems.Thm_DiffVI_Conv_lemma_7_1
-- name    : DiffVI.Conv.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:10.227919+00:00
-- url     : https://prove2.me/theorems/b030c848-dfb6-4880-a41a-f4450f0ee136
-- title:
--   Lemma 7.1, pp. 42–43 — the implicit Euler step has a unique solution x(u), with the bounds (7.4)
-- statement:
--   Let $T>0$ and let $(f,B,G)$ satisfy (A) and (B) on $\Omega=[0,T]\times\mathbb R^n$. Let $L_f>0$ be a Lipschitz constant of $f$ on $\Omega$, let $\rho_f>0$ satisfy the linear growth bound $\|f(t,x)\|\le\rho_f(1+\|x\|)$ on $\Omega$, and let $\sigma_B$ bound $\|B(t,x)\|$ on $\Omega$.
--
--   Then there is $h_0>0$ such that for all $h\in(0,h_0]$, $x^{\mathrm{ref}}\in\mathbb R^n$, $\theta\in[0,1]$ and $t,t_{\mathrm{ref}}\in[0,T]$:
--
--   1. for every $u\in\mathbb R^m$ there is a unique $x(u)\in\mathbb R^n$ with
--   $$x(u)-x^{\mathrm{ref}}=h\big[f(t,\theta x^{\mathrm{ref}}+(1-\theta)x(u))+B(t_{\mathrm{ref}},x^{\mathrm{ref}})u\big];$$
--   2. for all $u,u'$, $\displaystyle\|x(u)-x(u')\|\le\frac{h\sigma_B}{1-h(1-\theta)L_f}\|u-u'\|$;
--   3. for all $u$, $\displaystyle\|x(u)-x^{\mathrm{ref}}\|\le h\,\frac{\rho_f(1+\|x^{\mathrm{ref}}\|)+\sigma_B\|u\|}{1-h(1-\theta)\rho_f}$.
--
--   These are the bounds (7.4). The lemma makes the $x$-update of the time-stepping scheme (7.2) a well-defined, Lipschitz function of $u$, and gives the step-size bound used to control the iterates.
--
--   **Formalization Note** Items 2 and 3 are stated for any vectors $x,x'$ that satisfy the step equation for $u,u'$ (by item 1 these are $x(u),x(u')$). $L_f$, $\rho_f$, $\sigma_B$ are taken as named parameters with their defining inequalities, in addition to (A) and (B). One $h_0$ serves every $\theta\in[0,1]$, as the page states.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, pp. 42–43, Lemma 7.1, (7.4)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Conv_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace DiffVI.Conv

local notation "𝔼" k:max => EuclideanSpace ℝ (Fin k)

open SolodovSvaiterVI.Alg21

/-- Lemma 7.1 (pp. 42–43): solvability and the bounds (7.4) for the implicit Euler step. -/
theorem lemma_7_1 {n m : ℕ} (T : ℝ) (hT : 0 < T) (f : ℝ → 𝔼 n → 𝔼 n)
    (B : ℝ → 𝔼 n → (𝔼 m →L[ℝ] 𝔼 n)) (G : ℝ → 𝔼 n → 𝔼 m)
    (hA : DiffVI.Exist.CondA T f B G) (hB : DiffVI.Exist.CondB T B)
    (Lf ρf σB : ℝ) (hLf0 : 0 < Lf) (hLf : DiffVI.Exist.LipOnΩ T f Lf) (hρf0 : 0 < ρf)
    (hρf : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : 𝔼 n, ‖f t x‖ ≤ ρf * (1 + ‖x‖))
    (hσB : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : 𝔼 n, ‖B t x‖ ≤ σB) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h ∈ Set.Ioc (0 : ℝ) h0, ∀ xref : 𝔼 n, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ tref ∈ Set.Icc (0 : ℝ) T,
        (∀ u : 𝔼 m, ∃! x : 𝔼 n,
          x - xref = h • (f t (θ • xref + (1 - θ) • x) + B tref xref u)) ∧
        (∀ (u u' : 𝔼 m) (x x' : 𝔼 n),
          x - xref = h • (f t (θ • xref + (1 - θ) • x) + B tref xref u) →
          x' - xref = h • (f t (θ • xref + (1 - θ) • x') + B tref xref u') →
          ‖x - x'‖ ≤ h * σB / (1 - h * (1 - θ) * Lf) * ‖u - u'‖) ∧
        (∀ (u : 𝔼 m) (x : 𝔼 n),
          x - xref = h • (f t (θ • xref + (1 - θ) • x) + B tref xref u) →
          ‖x - xref‖ ≤ h * (ρf * (1 + ‖xref‖) + σB * ‖u‖) / (1 - h * (1 - θ) * ρf)) := by sorry

end DiffVI.Conv
