-- Prove2me | Theorems.Thm_DiscreteConvex_Combinatorial_matroid_axiom_correspondence
-- name    : DiscreteConvex.Combinatorial.matroid_axiom_correspondence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T20:27:24.852667+00:00
-- url     : https://prove2.me/theorems/4abd3c17-7532-4387-b4b4-ecd952dad91a
-- title:
--   Theorem 2.29 -- the matroid base-family / rank-function correspondence
-- statement:
--   **Theorem 2.29** (p.70). The class of set functions $\rho : 2^V \to \mathbb Z$ satisfying the rank axioms (R1)-(R3) and the class of nonempty families $\mathcal B \subseteq 2^V$ satisfying the simultaneous exchange axiom (B) are in one-to-one correspondence through the mutually inverse maps
--
--   $$\rho(X) = \max\{|X \cap J| : J \in \mathcal B\}, \qquad \mathcal B = \{J \subseteq V : \rho(J) = |J| = \rho(V)\}.$$
--
--   Concretely, the theorem asserts two things. First, starting from a nonempty exchange family $\mathcal B$, the induced rank function $\rho = \mathrm{RankOfFamily}(\mathcal B)$ satisfies (R1)-(R3), and recovering the family from $\rho$ returns $\mathcal B$ again. Second, starting from a rank function $\rho$ satisfying (R1)-(R3), the recovered family $\mathcal B = \mathrm{FamilyOfRank}(\rho)$ is nonempty, satisfies (B), and its own induced rank function is $\rho$ again.
--
--   This one-to-one correspondence is the finite-ground-set instance of the equivalence between exchangeability and submodularity that underlies matroid theory, and its generalization to functions on the integer lattice (M-convex functions) is the subject of later chapters of the book.
--
--   **Formalization Note.** The ground set $V$ is a `Fintype` with `DecidableEq`; $2^V$ is represented as `Finset (Finset V)`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Theorem 2.29.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Theorem 2.29

import Mathlib
import Definitions.Def_DiscreteConvex_Combinatorial_ExchangeFamily
import Definitions.Def_DiscreteConvex_Combinatorial_RankAxioms
import Definitions.Def_DiscreteConvex_Combinatorial_RankOfFamily
import Definitions.Def_DiscreteConvex_Combinatorial_FamilyOfRank

namespace DiscreteConvex.Combinatorial

/-- Theorem 2.29 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.70). The class of set
functions `ρ : Finset V → ℤ` satisfying the rank axioms (R1)-(R3) and the class of nonempty
families `𝓑 : Finset (Finset V)` satisfying the simultaneous exchange axiom (B) are in
one-to-one correspondence through the mutually inverse maps `RankOfFamily` (Eq. 2.71) and
`FamilyOfRank` (Eq. 2.72). -/
theorem matroid_axiom_correspondence {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ 𝓑 : Finset (Finset V), 𝓑.Nonempty → ExchangeFamily 𝓑 →
        RankAxioms (RankOfFamily 𝓑) ∧ FamilyOfRank (RankOfFamily 𝓑) = 𝓑) ∧
    (∀ ρ : Finset V → ℤ, RankAxioms ρ →
        (FamilyOfRank ρ).Nonempty ∧ ExchangeFamily (FamilyOfRank ρ) ∧
          RankOfFamily (FamilyOfRank ρ) = ρ) := by sorry

end DiscreteConvex.Combinatorial
