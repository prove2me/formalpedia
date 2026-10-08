-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSets_mconvex_set_iff_base_polyhedron
-- name    : DiscreteConvex.MConvexSets.mconvex_set_iff_base_polyhedron
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:21:05.960219+00:00
-- url     : https://prove2.me/theorems/8fd74a63-12f0-465f-bcce-8829996b58ec
-- title:
--   Theorem 4.15 -- M-convex sets correspond to integer submodular functions
-- statement:
--   **Theorem 4.15** (p.110). A nonempty set $B \subseteq \mathbb Z^V$ is M-convex if and only if $B = B(\rho) \cap \mathbb Z^V$ for some integer-valued submodular set function $\rho \in S[\mathbb Z]$, establishing a one-to-one correspondence between M-convex sets and integer-valued submodular set functions.
--
--   **Formalization Note.** The book additionally names the two mutually inverse maps realizing this correspondence explicitly ($\Phi(B)(X) = \sup\{x(X):x\in B\}$, Eq. (4.25)); this mission states the iff itself (an existential $\rho$) and does not construct $\Phi$ as a separate object.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.110, Theorem 4.15.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.110, Theorem 4.15

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSets_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSets_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegerValued

namespace DiscreteConvex.MConvexSets

/-- Theorem 4.15 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.110). A nonempty set
`B ⊆ Zⱽ` is M-convex if and only if `B = B(ρ) ∩ Zⱽ` for some integer-valued submodular set
function `ρ ∈ S[Z]`, establishing a one-to-one correspondence between M-convex sets and
integer-valued submodular set functions. -/
theorem mconvex_set_iff_base_polyhedron {V : Type*} [Fintype V] [DecidableEq V]
    (B : Set (V → ℤ)) (hB : B.Nonempty) :
    ExchangeAxiomB B ↔
      ∃ ρ : Finset V → WithTop ℝ, SubmodularSetFunction ρ ∧ IsIntegerValued ρ ∧
        B = {x : V → ℤ | (fun v => (x v : ℝ)) ∈ BasePolyhedron ρ} := by sorry

end DiscreteConvex.MConvexSets
