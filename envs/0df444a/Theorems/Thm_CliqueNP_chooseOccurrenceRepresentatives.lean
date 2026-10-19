-- Prove2me | Theorems.Thm_CliqueNP_chooseOccurrenceRepresentatives
-- name    : CliqueNP.chooseOccurrenceRepresentatives
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T08:06:14.015413+00:00
-- url     : https://prove2.me/theorems/c2bbae6e-7150-4fcb-b9a8-09a9e44ed9d7
-- title:
--   Choose witnesses coherently from pointwise witnesses
-- statement:
--   Turn pointwise witnesses of a property and an associated witness into a function of choices that preserves both properties.
-- source:
--   Richard M. Karp, Reducibility Among Combinatorial Problems, Complexity of Computer Computations, Plenum Press, pp. 85–103, 1972. https://doi.org/10.1007/978-1-4684-2001-2_9 . SAT-to-CLIQUE reduction, p. 97, restricted to clause width at most 3 (the language `KSat.KSAT 3`).

set_option autoImplicit false

theorem CliqueNP.chooseOccurrenceRepresentatives
    {α β γ : Type}
    (P : α → β → Prop)
    (Q : α → β → γ → Prop)
    (h : ∀ a, ∃ b, P a b ∧ ∃ c, Q a b c) :
    ∃ f : α → β, (∀ a, P a (f a)) ∧
      (∀ a, ∃ c, Q a (f a) c) := by sorry
