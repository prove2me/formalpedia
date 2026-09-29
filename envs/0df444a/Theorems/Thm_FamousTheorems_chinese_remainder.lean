-- Prove2me | Theorems.Thm_FamousTheorems_chinese_remainder
-- name    : FamousTheorems.chinese_remainder
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T01:51:10.050064+00:00
-- url     : https://prove2.me/theorems/27513934-db24-4413-a87e-37fb5a9d538a
-- title:
--   The Chinese remainder theorem
-- statement:
--   **The Chinese remainder theorem**, in its ring-theoretic form.
--
--   Let $R$ be a commutative ring and $(I_i)_{i \in \iota}$ a finite family of pairwise coprime ideals.
--   Then
--   $$R \big/ \textstyle\bigcap_i I_i \;\cong\; \prod_i R/I_i$$
--   as rings.
--
--   Taking $R = \mathbb{Z}$ and $I_i = (n_i)$ with the $n_i$ pairwise coprime recovers the classical
--   statement: a system of congruences $x \equiv a_i \pmod{n_i}$ has a solution, unique modulo
--   $\prod n_i$. The abstract version makes clear what is really going on — coprimality is exactly the
--   condition for the natural map to $\prod R/I_i$ to be surjective, and the intersection is the kernel.
--
--   The theorem appears in Sun Tzu's *Sunzi Suanjing* (3rd–5th century), with the general method given
--   by Qin Jiushao in 1247. It is the reason modular arithmetic decomposes into prime-power components,
--   underlies fast multiplication by residue number systems, Lagrange interpolation (the polynomial
--   case), and the decomposition of a finite abelian group into its Sylow subgroups.
--
--   **Formalization note.** `IsCoprime I J` means $I + J = R$, and `⨅` is the intersection of the family.
--   The equivalence is packaged as `Nonempty` because the Mathlib result is a ring isomorphism (data)
--   rather than a proposition. The result is Mathlib's `Ideal.quotientInfRingEquivPiQuotient`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem chinese_remainder {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (f : ι → Ideal R) (hf : Pairwise (Function.onFun IsCoprime f)) :
    Nonempty ((R ⧸ ⨅ i, f i) ≃+* ∀ i, R ⧸ f i) := by sorry

end FamousTheorems
