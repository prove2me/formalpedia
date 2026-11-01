-- Prove2me | Theorems.Thm_ConvStochDual_Existence_pp13_lemma_22
-- name    : ConvStochDual.Existence.pp13_lemma_22
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-01T03:07:15.947607+00:00
-- url     : https://prove2.me/theorems/d2458714-16c2-4ffc-b95f-8ff992bff368
-- title:
--   Lemma 22 of Pennanen–Perkkiö (2022) — adapted strategies pair to zero with $\mathcal N^\perp$ when $(x\cdot v)^+\in L^1$
-- statement:
--   This is the key "generalized martingale" lemma used to obtain weak duality for problems over general (possibly non-integrable) adapted strategies.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $\mathcal F_0\subseteq\mathcal F_1\subseteq\cdots\subseteq\mathcal F_T\subseteq\mathcal F$. Each of the $n$ coordinates of a decision vector is assigned a decision time $\tau(i)\in\{0,\dots,T\}$. Let $x:\Omega\to\mathbb R^n$ be **adapted**, i.e. each coordinate $x_i$ is (a.s. equal to) an $\mathcal F_{\tau(i)}$-measurable random variable, with no integrability assumption. Let $v:\Omega\to\mathbb R^n$ have integrable coordinates and be orthogonal to the adapted strategies in the sense that
--
--   $$\mathbb E\big[v_i\,\big|\,\mathcal F_{\tau(i)}\big]=0\quad\text{a.s. for every } i.$$
--
--   If the positive part $(x\cdot v)^+$ is integrable, then $x\cdot v$ is integrable and
--
--   $$\mathbb E[x\cdot v]=0.$$
--
--   In the notation of the source, $x\in\mathcal N$ and $v\in\mathcal N^\perp$; the lemma shows that the shadow price of information $v$ prices every adapted strategy at zero as soon as the pairing is quasi-integrable from above.
--
--   **Formalization Note** The orthogonality $v\in\mathcal N^\perp$ is expressed coordinatewise through conditional expectations, which is equivalent to $\mathbb E[w\cdot v]=0$ for all bounded adapted $w$. Integrability of $(x\cdot v)^+$ is stated as finiteness of the lower Lebesgue integral of $\max(x\cdot v,0)$.
-- source:
--   T. Pennanen and A.-P. Perkkiö, Duality in convex stochastic optimization, arXiv:2205.02045v1, p. 16, Lemma 22 (used in the proof of Lemma 21); cited as [13] in arXiv:2205.15825v1

import Mathlib

open MeasureTheory

namespace ConvStochDual.Existence

/-- Pennanen–Perkkiö, Duality in convex stochastic optimization, arXiv:2205.02045v1,
p. 16, Lemma 22: if `x` is adapted, `v` is orthogonal to the adapted strategies
(`E[v_i | 𝓕_{τ i}] = 0`) and `(x · v)⁺` is integrable, then `E[x · v] = 0`. -/
theorem pp13_lemma_22 {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {T n : ℕ} (τ : Fin n → Fin (T + 1))
    (𝔽 : Fin (T + 1) → MeasurableSpace Ω)
    (h𝔽le : ∀ t, 𝔽 t ≤ mΩ) (h𝔽mono : Monotone 𝔽)
    (x v : Ω → Fin n → ℝ)
    (hx : ∀ i, ∃ g : Ω → ℝ, StronglyMeasurable[𝔽 (τ i)] g ∧ (fun ω => x ω i) =ᵐ[P] g)
    (hv : ∀ i, Integrable (fun ω => v ω i) P)
    (hperp : ∀ i, P[fun ω => v ω i | 𝔽 (τ i)] =ᵐ[P] 0)
    (hpos : ∫⁻ ω, ENNReal.ofReal (∑ i, x ω i * v ω i) ∂P ≠ ⊤) :
    Integrable (fun ω => ∑ i, x ω i * v ω i) P ∧ ∫ ω, ∑ i, x ω i * v ω i ∂P = 0 := by sorry

end ConvStochDual.Existence
