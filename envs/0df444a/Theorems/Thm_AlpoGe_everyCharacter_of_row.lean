-- Prove2me | Theorems.Thm_AlpoGe_everyCharacter_of_row
-- name    : AlpoGe.everyCharacter_of_row
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-21T16:43:21.044728+00:00
-- url     : https://prove2.me/theorems/e1da288d-e43c-4aad-9426-dbbba4ff8418
-- title:
--   alpo.ge GRH release: Row0b implies L(χ, s) ≠ 0 for every Dirichlet character χ and Re(s) > 1/2
-- statement:
--   If the proposition $\mathcal R$ = `UpperTheory.GalStar.Row0b (fun h rc => UpperTheory.Zero.LLC.IsRecT h rc)` holds (stated on its own as `AlpoGe.galoisLocalGlobalStrong_recParameter`: Galois representations attached to regular algebraic polarized cuspidal representations of $\mathrm{GL}_a$ over CM fields, with local–global compatibility), then for every modulus $N\ge1$, every Dirichlet character $\chi$ modulo $N$ with values in $\mathbb C$, and every $s\in\mathbb C$ with $\operatorname{Re}s>\tfrac12$ and ($\chi\ne1$ or $s\ne1$),
--   $$L(\chi,s)\neq0.$$
--
--   This is the release's `UpperTheory.FinalTheorems.everyCharacter_of_row` (L. Alpöge, written with Claude, 20 November 2026), whose conclusion `UpperTheory.EveryCharacter` is written out here in Mathlib's terms. The release's main theorem is this implication applied to its proof of $\mathcal R$.
--
--   **Formalization note.** $L(\chi,s)$ is Mathlib's `DirichletCharacter.LFunction`, the analytic continuation of $\sum_{n\ge1}\chi(n)n^{-s}$; at the pole $\chi=1$, $s=1$ it takes an unspecified finite value, and that point is excluded. The region includes $\operatorname{Re}s\ge1$. For $N=1$ the conclusion is the Riemann hypothesis in half-plane form, and the conclusion is equivalent to the GRH mission's goal `GRH.dirichlet_zero_free_bound` (which writes the exclusion as $\neg(\chi=1\wedge s=1)$).
-- source:
--   L. Alpöge, working with Claude, Lean formalization of the Riemann hypothesis and of GRH for Dirichlet L-functions, released 20 November 2026 (announcement https://alpo.ge/remark.pdf; Lean archive https://alpo.ge/lean.tar.gz.part01 to part14, joined tarball sha256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc); the release's UpperTheory.FinalTheorems.everyCharacter_of_row, with UpperTheory.EveryCharacter written out

import Mathlib
import Definitions.Def_AlpoGeB008

section

namespace AlpoGe

theorem everyCharacter_of_row
    (H : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0 := by
  sorry

end AlpoGe
end
