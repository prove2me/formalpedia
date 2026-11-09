-- Prove2me | Theorems.Thm_DerandLDT_corollary_3_13
-- name    : DerandLDT.corollary_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:22.104507+00:00
-- url     : https://prove2.me/theorems/1baa9179-1df9-4b7e-b037-9109835de1ed
-- title:
--   Corollary 3.13 — over any field, $\mathrm{Disc}(f) \ne 0$ iff $f$ is separable, and then $f$ is squarefree (corrected: separable)
-- statement:
--   Let $\mathbb F$ be any field and $f \in \mathbb F[X]$ a polynomial of degree at least two whose first-order Hasse derivative $\partial f$ is nonzero and of degree at least one. Then
--
--   1. $\mathrm{Disc}(f) \neq 0$ if and only if $f$ is separable, i.e. $\gcd(f, \partial f) = 1$;
--   2. if $\mathrm{Disc}(f) \neq 0$, then $f$ is squarefree.
--
--   The paper applies the corollary to polynomials over fields of rational functions, which need not be perfect.
--
--   **Formalization Note** $\mathrm{Disc}$ is `DerandLDT.disc` and separability is `Polynomial.Separable` (coprimality of $f$ and its derivative).
--
--   Differences from the source:
--   - correction: f is squarefree if and only if Disc(f) is non-zero → (Disc f ≠ 0 ↔ f separable) ∧ (Disc f ≠ 0 → f squarefree); reason: squarefree ⟹ Disc ≠ 0 is false over imperfect fields: over F_p(T), f = Z(Z^p − T) has degree p + 1 ≥ 2, ∂f = Z^p − T nonzero of degree p ≥ 1, f squarefree, yet gcd(f, ∂f) = Z^p − T so Disc(f) = 0; the true direction is kept and the exact characterization (separable) is stated
--   - encoding: Disc(f) via the Sylvester matrix of Definition 3.10 → Mathlib's resultant with default sizes deg f, deg ∂f; reason: the same matrix under the hypotheses deg f ≥ 2 and deg ∂f ≥ 1
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Corollary 3.13, p.13

import Definitions.Def_DerandLDT_disc

set_option autoImplicit false

universe u

namespace DerandLDT

open Polynomial

/-- **Corollary 3.13** (discriminant over an arbitrary field), corrected. Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point
low-degree test*, STOC 2027 submission manuscript (sha256 d57e7d6f…80df),
Corollary 3.13, p.13: *Let `F` be any field and `f ∈ F[X]` of degree at least two such that the
Hasse derivative `∂(f)` is nonzero and has degree at least one. Then `f` is squarefree iff
`Disc(f)` is nonzero.*

**Formalization Note.** The printed direction "squarefree ⟹ `Disc(f) ≠ 0`" is false over
imperfect fields: over `F = F_p(T)`, `f = Z(Z^p − T)` has degree `p + 1 ≥ 2`, `∂f = Z^p − T` is
nonzero of degree `p ≥ 1`, and `f` is squarefree (`Z` and `Z^p − T` are distinct irreducibles),
yet `gcd(f, ∂f) = Z^p − T`, so `Disc(f) = 0`. The corrected statement keeps the true direction
`Disc(f) ≠ 0 ⟹ f squarefree` and states the exact characterization `Disc(f) ≠ 0 ⟺ f separable`
(`gcd(f, ∂f) = 1`). `Disc` is `DerandLDT.disc` (Definition 3.10). -/
theorem corollary_3_13 (F : Type u) [Field F] (f : F[X]) (hf : 2 ≤ f.natDegree)
    (hd : hasseDeriv 1 f ≠ 0) (hd1 : 1 ≤ (hasseDeriv 1 f).natDegree) :
    (disc f ≠ 0 ↔ f.Separable) ∧ (disc f ≠ 0 → Squarefree f) := by sorry

end DerandLDT
