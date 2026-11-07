-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_6_4
-- name    : AdaptiveSparsify.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:28.518319+00:00
-- url     : https://prove2.me/theorems/d6ead328-970f-49ef-adfc-c1a4f6d7bc91
-- title:
--   Lemma 6.4 — the final point: a well-centered pair projects to a feasible point with gap $O(nt)$
-- statement:
--   Let $(x,s)$ be $\varepsilon$ well-centered at $t$. Put $s^{(\mathrm{final})}=s$ and
--
--   $$x^{(\mathrm{final})}=x-\nabla^2\Phi(x)^{-1}A\big(A^\top\nabla^2\Phi(x)^{-1}A\big)^{-1}(A^\top x-b).$$
--
--   Then $x^{(\mathrm{final})}_i\in K_i$ for all $i$, $A^\top x^{(\mathrm{final})}=b$, $s^{(\mathrm{final})}=c-Ay$ for some $y$, and for every feasible point $y'$,
--
--   $$c^\top x^{(\mathrm{final})}-c^\top y'\le C\,n\,t,$$
--
--   where $C$ depends only on $C_K$. This is how the interior point method ends: at $t\approx\varepsilon/n$ it returns an exactly feasible, $\varepsilon$-optimal point.
--
--   Differences from the source:
--   - reading: "we can compute a feasible pair" → the explicit formula of the proof, with x^{(final)} ∈ K₁ × ⋯ × K_m stated; reason: the proof defines the pair this way; the running time is carried by Theorem 1
--   - reading: the minimum over feasible points → a bound against every feasible point; reason: reading R7: no junk value of an infimum
--   - reading: ≲ nt → C n t, with C depending on C_K only; reason: the constant of the barrier parameters, p.45
--   - reading: §4 assumes n large enough for log n > 0 → n ≥ 2; reason: λ = C_center log n / ε² vanishes at n = 1 and α is then undefined
--   - reading: "ε-well-centered" for §4's ε and C_center → ε < 1/80 (p.17), C_center ≥ 1; reason: under which α is small, as the proof needs
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Lemma 6.4, p.43

import Mathlib
import Definitions.Def_AdaptiveSparsify_IPM

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 6.4** (Final point), p.43.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Lemma 6.4, p.43.

"Given an ε-well-centered point (x, s) for path parameter t, we can compute a feasible pair
(x^{(final)}, s^{(final)}) such that: 1. A⊤x^{(final)} = b and s^{(final)} = c − Ay for some y ∈ R^d, and
2. c⊤x^{(final)} − min_{x∈K_1×···×K_m, A⊤x=b} c⊤x ≲ nt,"

**Formalization Note.** "Compute" is the explicit formula of the proof: `s^{(final)} = s` and
`x^{(final)} = x − ∇²Φ(x)⁻¹A(A⊤∇²Φ(x)⁻¹A)⁻¹(A⊤x − b)`. The minimum becomes `∀` feasible `y` (reading R7). The
constant depends on `C_K` only. Here `ε < 1/80` (p.17) and `C_center ≥ 1`, so `α` is small. -/
theorem lemma_6_4 : ∀ CK : ℕ, 1 ≤ CK → ∃ C : ℝ, 0 < C ∧
    ∀ (ε Cc : ℝ), 0 < ε → ε < 1 / 80 → 1 ≤ Cc →
    ∀ I : ERMInstance, I.IsAdmissible CK → 2 ≤ I.blocks.n →
    ∀ (t : ℝ) (x s : Fin I.blocks.n → ℝ), 0 < t →
      let p : Params := ⟨CK, ε, Cc⟩
      I.WellCentered (p.alpha I.blocks.n) ε t x s →
      let xf := x - ((I.hessΦ x)⁻¹ * I.A * (I.schur x)⁻¹) *ᵥ (I.Aᵀ *ᵥ x - I.b)
      I.Feasible xf ∧ (∃ y : Fin I.d → ℝ, s = I.c - I.A *ᵥ y) ∧
      ∀ y, I.Feasible y → I.c ⬝ᵥ xf - I.c ⬝ᵥ y ≤ C * (I.blocks.n : ℝ) * t := by sorry

end AdaptiveSparsify
