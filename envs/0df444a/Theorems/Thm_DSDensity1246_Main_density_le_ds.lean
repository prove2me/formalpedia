-- Prove2me | Theorems.Thm_DSDensity1246_Main_density_le_ds
-- name    : DSDensity1246.Main.density_le_ds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:12:35.625691+00:00
-- url     : https://prove2.me/theorems/e8224665-9823-4de0-b69b-2291811b8f41
-- title:
--   Theorem 1 — Maximum list density is bounded by DS dimension
-- statement:
--   Let $X$ and $Y$ be arbitrary sets, and let $H\subseteq Y^X$ be any hypothesis class. Fix integers $\ell\ge1$ and $n>0$. Write $d^\ell_{\rm DS}(H)$ for the supremum of the lengths of sequences $\ell$-DS shattered by $H$, and $\mu_H^\ell(n)$ for the supremum of the $\ell$-densities of all finite nonempty subfamilies of all length-$n$ restrictions of $H$. Then
--
--   $$\left\lceil\mu_H^\ell(n)\right\rceil\le d^\ell_{\rm DS}(H).$$
--
--   The constant is exactly one and the ceiling is retained. In particular, if the dimension equals a natural number $d$, the natural ceiling of the maximum density is at most $d$. There are no finiteness, countability, nonemptiness, distributional, or algorithmic assumptions on $X,Y,H$. The inequality also holds when the dimension is infinite.
--
--   This is the submission's main structural result, separating the combinatorial target from its downstream learning and sample-compression consequences.
--
--   Differences from the source:
--   - generalization: dimension d^ℓ_DS described as an integer in the proof on p. 16 → dimension in ℕ∞ with all hypothesis classes quantified, including unbounded dimension and the empty class (dimension 0, where the source's "largest integer" is undefined); reason: every finite-dimensional source instance is unchanged, the additional infinite-dimensional case has right-hand side ⊤, and the empty class has μ = 0
--   - encoding: length-n sequences and finite nonempty restricted families → Fin n sequences and Finset families inside the published projection; reason: the same objects with zero-based coordinate indices; repeated points and arbitrary label types remain allowed
--   - encoding: nonnegative density supremum and its ceiling → bounded nonnegative-real supremum with empty value zero and its natural ceiling cast into ℕ∞; reason: each density is unconditionally at most n, so the real supremum and ceiling agree; the empty convention covers absent eligible samples or families
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), p. 3, Theorem 1 (Density upper-bounded by DS), Eq. (6); restatement p. 14, proof pp. 14–16

import Definitions.Def_DSDensity1246_Main_dsModel
import Definitions.Def_DSDensity1246_Main_maximumDensity

namespace DSDensity1246.Main

/-- Theorem 1, pp. 3 and 14, (6): constant 1 and the ceiling are retained.
The extended-natural dimension also covers unbounded shattering. -/
theorem density_le_ds {X Y : Type*} (H : Set (X → Y))
    (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (hn : 0 < n) :
    (⌈(maximumDensity ℓ H n : ℝ)⌉₊ : ℕ∞) ≤ listDSDim ℓ H := by sorry

end DSDensity1246.Main
