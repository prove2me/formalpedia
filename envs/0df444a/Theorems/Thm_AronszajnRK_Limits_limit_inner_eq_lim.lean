-- Prove2me | Theorems.Thm_AronszajnRK_Limits_limit_inner_eq_lim
-- name    : AronszajnRK.Limits.limit_inner_eq_lim
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:12:20.204988+00:00
-- url     : https://prove2.me/theorems/4bd7152e-abe6-4ba3-acd4-5de4ee9249be
-- title:
--   §9, proof of Theorem I, Eq. (7) — $(f_0,g_0)_0=\lim_n (f_{0n},g_{0n})_n$
-- statement:
--   Assume the standing assumptions (1)–(3) of §9 A. Let $F_0$ be a complex inner product space of functions on $E$ in which point evaluations are continuous, whose norm is the limit norm of Theorem I: for every $f_0\in F_0$ the restrictions $f_{0n}$ belong to $F_n$ and
--
--   $$\|f_0\|_0=\lim_{n\to\infty}\|f_{0n}\|_n .$$
--
--   Then for all $f_0,g_0\in F_0$ the scalar products converge as well:
--
--   $$(f_0,g_0)_0=\lim_{n\to\infty}(f_{0n},g_{0n})_n .$$
--
--   In the proof of Theorem I this identity is what transfers the reproducing property of the $K_n$ to $K_0$.
--
--   **Formalization Note** In the paper the scalar product of $F_0$ is obtained from the limit norm; here $F_0$ is given as an inner product space whose norm is assumed to be that limit, and the conclusion is the convergence of scalar products. Aronszajn's $(f,g)$ is linear in $f$; Mathlib's $\langle g,f\rangle$ is the same number, so the statement reads $\langle g_{0n}, f_{0n}\rangle\to\langle g_0,f_0\rangle$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 364, §9, proof of Theorem I, Eq. (7)

import Mathlib
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence

open Filter Topology
open scoped InnerProductSpace

namespace AronszajnRK.Limits

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §9, proof of
Theorem I, Eq. (7), p. 364, PDF p. 28: `(f₀, g₀)₀ = lim_{n→∞} (f₀ₙ, g₀ₙ)ₙ`.

Under the standing assumptions (1)–(3) of §9 A, let `H₀` be a complex inner product space of
functions on `E = X` whose norm is the limit norm of Theorem I: for every `f₀ ∈ H₀` and every
sequence `g` of restrictions (`g n ∈ H n` has the function `f₀` restricted to `E n`),
`‖g n‖ → ‖f₀‖`. Then the scalar products of restrictions converge to the scalar product in `H₀`.
Aronszajn's `(f, g)` is linear in `f`; Mathlib's `⟪g, f⟫_ℂ` is the same number, so `(f₀, g₀)₀`
is `⟪g₀, f₀⟫_ℂ` and `(f₀ₙ, g₀ₙ)ₙ` is `⟪b n, a n⟫_ℂ`. -/
theorem limit_inner_eq_lim {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H)
    (H₀ : Type*) [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [RKHS ℂ H₀ X ℂ]
    (hnorm : ∀ (f₀ : H₀) (g : ∀ n, H n), (∀ (n : ℕ) (x : E n), g n x = f₀ x.1) →
      Tendsto (fun n => ‖g n‖) atTop (𝓝 ‖f₀‖))
    (f₀ g₀ : H₀) (a b : ∀ n, H n) (ha : ∀ (n : ℕ) (x : E n), a n x = f₀ x.1)
    (hb : ∀ (n : ℕ) (x : E n), b n x = g₀ x.1) :
    Tendsto (fun n => ⟪b n, a n⟫_ℂ) atTop (𝓝 ⟪g₀, f₀⟫_ℂ) := by sorry

end AronszajnRK.Limits
