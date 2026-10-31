-- Prove2me | Theorems.Thm_CoCoNet_proposition_2
-- name    : CoCoNet.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:17.910873+00:00
-- url     : https://prove2.me/theorems/3cf0edca-c563-4995-aaa8-e53082af31e4
-- title:
--   Proposition 2 — a multivariate intermediate value theorem
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$ be continuous, with
--   1. for every $i$, $f_i(x)$ weakly increasing in $x_i$ and weakly decreasing in each $x_j$, $j\ne i$;
--   2. for every $i$, $\lim_{t\to\infty}f_i(te)=+\infty$ and $\lim_{t\to\infty}f_i(-te)=-\infty$, where $e=(1,\dots,1)$.
--
--   Then $f$ is surjective: for every $y\in\mathbb R^n$ there is $x$ with $f(x)=y$.
--
--   It is applied to the fair map $\Phi$ to obtain Proposition 3.
--
--   **Formalization Note** Monotonicity in $x_i$ is monotonicity of $t\mapsto f_i(x \text{ with } x_i:=t)$ for every $x$ (`Function.update`).
--
--   Differences from the source:
--   - encoding: 'weakly increasing in xᵢ and weakly decreasing in xⱼ'; limits along ±te → Monotone / Antitone of t ↦ fᵢ(Function.update x i t); Tendsto along atTop to atTop / atBot; reason: the standard meaning
--   - encoding: indices [n] = {1, …, n}; vectors in ℝⁿ → indices Fin n (0-based); vectors Fin n → ℝ; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, Proposition 2, p.17

import Mathlib

namespace CoCoNet

open Filter

/-- **Proposition 2 (a multivariate intermediate value theorem).**
Balter, Schweizer & Vera, arXiv:2011.06474v1, Proposition 2, p.17: "Let f : ℝⁿ → ℝⁿ,
f(x) = (f₁(x₁, …, xₙ), …, fₙ(x₁, …, xₙ)), be a continuous function with the following
properties: (i) For all i ∈ [n], fᵢ(x) is weakly increasing in xᵢ and weakly decreasing in xⱼ,
j ≠ i. (ii) For all i ∈ [n], we have lim_{t→∞} fᵢ(te) = ∞ and lim_{t→∞} fᵢ(−te) = −∞. Then f is
surjective, i.e., for every y ∈ ℝⁿ there exists x ∈ ℝⁿ such that f(x) = y."

**Formalization Note.** "Weakly increasing in xᵢ" is monotonicity of `t ↦ fᵢ(x with xᵢ := t)` for
every `x` (`Function.update`); `e` is the all-ones vector, so `te = fun _ => t`. -/
theorem proposition_2 {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf : Continuous f)
    (hinc : ∀ (x : Fin n → ℝ) (i : Fin n), Monotone fun t : ℝ => f (Function.update x i t) i)
    (hdec : ∀ (x : Fin n → ℝ) (i j : Fin n), j ≠ i →
      Antitone fun t : ℝ => f (Function.update x j t) i)
    (htop : ∀ i, Tendsto (fun t : ℝ => f (fun _ => t) i) atTop atTop)
    (hbot : ∀ i, Tendsto (fun t : ℝ => f (fun _ => -t) i) atTop atBot) :
    Function.Surjective f := by sorry

end CoCoNet
