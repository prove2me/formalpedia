-- Prove2me | Theorems.Thm_AronszajnRK_Limits_decreasing_limit_kernel
-- name    : AronszajnRK.Limits.decreasing_limit_kernel
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:13:46.454995+00:00
-- url     : https://prove2.me/theorems/34678248-8d6f-4271-b967-b971756af645
-- title:
--   §9, Theorem I — the kernels $K_n$ of a decreasing sequence of classes converge to the r.k. $K_0$ of the limit class $F_0$
-- statement:
--   Let $E_1\subset E_2\subset\cdots$ be sets with union $E$, and for each $n$ let $F_n$ be a complex Hilbert space of functions on $E_n$ with norm $\|\cdot\|_n$ and reproducing kernel $K_n$. Assume that the classes decrease and the norms increase: for $f_n\in F_n$ and $m\le n$, the restriction $f_{nm}$ of $f_n$ to $E_m$ belongs to $F_m$ and $\|f_{nm}\|_m\le\|f_n\|_n$.
--
--   Then the kernels converge to a kernel $K_0(x,y)$ defined for all $x,y\in E$: if $x,y\in E_N$, then
--
--   $$\lim_{n\to\infty} K_n(x,y) = K_0(x,y)$$
--
--   (the terms being defined for $n\ge N$). Moreover $K_0$ is the reproducing kernel of the class $F_0$ of all functions $f_0$ on $E$ such that
--
--   1. (1°) the restrictions $f_{0n}$ of $f_0$ to $E_n$ belong to $F_n$ for every $n$, and
--   2. (2°) $\lim_{n\to\infty}\|f_{0n}\|_n<\infty$,
--
--   the norm of $f_0\in F_0$ being
--
--   $$\|f_0\|_0=\lim_{n\to\infty}\|f_{0n}\|_n .$$
--
--   The theorem describes how reproducing kernels behave under a monotone limit of the underlying classes; the special case $E_n=E$ for all $n$ (a decreasing sequence of classes $F_1\supset F_2\supset\cdots$ on one set) is included.
--
--   **Formalization Note** The conclusion has three parts: (a) there is $K_0$ with the pointwise convergence above; (b) some reproducing kernel Hilbert space on $E$ has scalar kernel $K_0$; (c) every reproducing kernel Hilbert space on $E$ with scalar kernel $K_0$ consists exactly of the functions of $F_0$ (`limitClass`), and the norm of each of its elements $f_0$ is $\lim_n\|f_{0n}\|_n$. By Moore's uniqueness of the space with a given kernel (§2 (4)), (b) and (c) together say that $K_0$ is the reproducing kernel of $F_0$ with the limit norm. The space in (b) is taken in the universe of $E$; (c) quantifies over spaces in any universe. Indexing starts at $0$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), pp. 362–363, §9, Theorem I (convergence in the sense of the proof, p. 363)

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence
import Definitions.Def_AronszajnRK_Limits_limitClass

open Filter Topology

namespace AronszajnRK.Limits

universe u v w

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §9, Theorem I,
pp. 362–363, PDF pp. 26–27, with the meaning of the convergence fixed in its proof (p. 363).

Under the standing assumptions (1)–(3) of §9 A (`IsDecreasingRKSequence`) and the existence of the
reproducing kernels `Kₙ` of the classes `H n` on `E n`, there is a kernel `K₀` on `E = X` with:

* the kernels converge to `K₀`: for `x, y ∈ E N`, `K_{N+j}(x, y) → K₀(x, y)` as `j → ∞`
  (`Kₙ(x, y)` is defined only once `x, y ∈ E n`);
* `K₀` is the reproducing kernel of a Hilbert space of functions on `X`; and
* every such space `H₀` (by Moore's uniqueness, §2 (4), there is only one) consists exactly of the
  functions of the limit class `F₀` (`limitClass E H`), and the norm of `f₀ ∈ H₀` is
  `lim_{n→∞} ‖f₀ₙ‖ₙ`, where `f₀ₙ ∈ H n` is the restriction of `f₀` to `E n`. -/
theorem decreasing_limit_kernel {X : Type u} (E : ℕ → Set X) (H : ℕ → Type v)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) :
    ∃ K₀ : X → X → ℂ,
      (∀ (x y : X) (N : ℕ) (hx : x ∈ E N) (hy : y ∈ E N),
        Tendsto (fun j : ℕ => AronszajnRK.Sum.kernelFn (H (N + j)) ⟨x, hS.mono (Nat.le_add_right N j) hx⟩
          ⟨y, hS.mono (Nat.le_add_right N j) hy⟩) atTop (𝓝 (K₀ x y))) ∧
      (∃ (H₀ : Type u) (_ : NormedAddCommGroup H₀) (_ : InnerProductSpace ℂ H₀)
          (_ : CompleteSpace H₀) (_ : RKHS ℂ H₀ X ℂ), ∀ x y : X, AronszajnRK.Sum.kernelFn H₀ x y = K₀ x y) ∧
      ∀ (H₀ : Type w) [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
        [RKHS ℂ H₀ X ℂ], (∀ x y : X, AronszajnRK.Sum.kernelFn H₀ x y = K₀ x y) →
        Set.range (fun f : H₀ => (⇑f : X → ℂ)) = limitClass E H ∧
        ∀ (f₀ : H₀) (g : ∀ n, H n), (∀ (n : ℕ) (x : E n), g n x = f₀ x.1) →
          Tendsto (fun n => ‖g n‖) atTop (𝓝 ‖f₀‖) := by sorry

end AronszajnRK.Limits
