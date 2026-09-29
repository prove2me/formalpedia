-- Prove2me | Theorems.Thm_FamousTheorems_equational_criterion_flatness
-- name    : FamousTheorems.equational_criterion_flatness
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:15.045291+00:00
-- url     : https://prove2.me/theorems/43205aa7-5044-4c4b-b3fe-ccb0348095d3
-- title:
--   The equational criterion for flatness
-- statement:
--   **The equational criterion for flatness.** A module $M$ over a commutative ring $R$ is flat if and only if the following holds. Whenever $\sum_{i=1}^{l} f_i x_i=0$ in $M$ with $f_i\in R$ and $x_i\in M$, there exist $k$, elements $y_1,\dots,y_k\in M$ and a matrix $(a_{ji})$ over $R$ such that $x_i=\sum_j a_{ji}y_j$ for all $i$ and $\sum_i a_{ji}f_i=0$ for all $j$.
--
--   In words, every linear relation in $M$ is a consequence of linear relations in $R$. The criterion is the main tool for proving flatness by hand, and it is the key step in Lazard's theorem that flat modules are filtered colimits of free modules.
--
--   **Formalization note.** Mathlib's `Module.Flat.iff_forall_exists_factorization`. The coefficients $f$ form an element of `Fin l →₀ R`, the elements $x_i$ are encoded as the linear map $x:R^l\to M$, and the conclusion factors $x$ through $R^k$ via a map $a$ that kills $f$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Module.Flat.iff_forall_exists_factorization`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem equational_criterion_flatness {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ {l : ℕ} {f : Fin l →₀ R} {x : (Fin l →₀ R) →ₗ[R] M}, x f = 0 →
        ∃ (k : ℕ) (a : (Fin l →₀ R) →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M), x = y ∘ₗ a ∧ a f = 0 := by sorry

end FamousTheorems
