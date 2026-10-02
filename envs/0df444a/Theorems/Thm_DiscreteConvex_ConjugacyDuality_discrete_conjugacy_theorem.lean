-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDuality_discrete_conjugacy_theorem
-- name    : DiscreteConvex.ConjugacyDuality.discrete_conjugacy_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:11:50.540968+00:00
-- url     : https://prove2.me/theorems/d9427bdf-0f99-4e48-b7b5-e8fc8e257e8e
-- title:
--   Theorem 8.12 -- the discrete conjugacy theorem
-- statement:
--   **Theorem 8.12** (p.212). (1) The classes of integer-valued M-convex functions $M[\mathbb Z\to\mathbb Z]$ and integer-valued L-convex functions $L[\mathbb Z\to\mathbb Z]$ are in one-to-one correspondence under the discrete Legendre-Fenchel transformation: for $f \in M[\mathbb Z\to\mathbb Z]$ and $g \in L[\mathbb Z\to\mathbb Z]$, $f^\bullet \in L[\mathbb Z\to\mathbb Z]$, $g^\bullet \in M[\mathbb Z\to\mathbb Z]$, $f^{\bullet\bullet}=f$, and $g^{\bullet\bullet}=g$. (2) The same correspondence holds for the M$^\natural$/L$^\natural$ pair.
--
--   This is the unifying theorem of the whole book: it shows the M-convex-function theory (chunks 06–07) and the L-convex-function theory (chunks 08–09) are not two independent developments but two faces of a single conjugacy, exactly generalizing the classical fact that the Legendre-Fenchel transform is an involution on closed proper convex functions. Unlike the real-valued (polyhedral) conjugacy theorem it builds on, the *integer* bijection is a genuinely harder, separate fact: its proof needs the M-/L-proximity theorems (chunks 06–09) to control what happens to integrality under convex extension and re-discretization.
--
--   **Formalization Note.** $f^\bullet$ uses the discrete transform $(8.11)_{\mathbb Z}$ (supremum over $x \in \mathbb Z^V$ for $p \in \mathbb Z^V$), distinct from the real-valued transform $(8.3)$ used by the (unformalized in this mission) polyhedral conjugacy theorem — the two are never conflated.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Theorem 8.12.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Theorem 8.12

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDuality_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctions_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctions_LNaturalConvex

namespace DiscreteConvex.ConjugacyDuality

/-- Theorem 8.12, the discrete conjugacy theorem (Murota, *Discrete Convex Analysis*, SIAM
2003, p.212). (1) The classes of integer-valued M-convex functions `M[Z→Z]` and integer-valued
L-convex functions `L[Z→Z]` are in one-to-one correspondence under the discrete
Legendre-Fenchel transformation: for `f ∈ M[Z→Z]` and `g ∈ L[Z→Z]`, `f• ∈ L[Z→Z]`,
`g• ∈ M[Z→Z]`, `f•• = f`, and `g•• = g`. (2) The same holds for the M♮/L♮ pair. -/
theorem discrete_conjugacy_theorem {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ f : (V → ℤ) → WithTop ℝ, DiscreteConvex.MConvexFunctions.MExchangeAxiom f →
        IsIntegerValued f →
        DiscreteConvex.LConvexFunctions.SBF (ConvexConjugate f) ∧
          DiscreteConvex.LConvexFunctions.TRF (ConvexConjugate f) ∧
          IsIntegerValued (ConvexConjugate f) ∧
          ConvexConjugate (ConvexConjugate f) = f) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, DiscreteConvex.LConvexFunctions.SBF g →
        DiscreteConvex.LConvexFunctions.TRF g → IsIntegerValued g →
        DiscreteConvex.MConvexFunctions.MExchangeAxiom (ConvexConjugate g) ∧
          IsIntegerValued (ConvexConjugate g) ∧
          ConvexConjugate (ConvexConjugate g) = g) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, DiscreteConvex.MConvexFunctions.MNaturalConvex f →
        IsIntegerValued f →
        DiscreteConvex.LConvexFunctions.LNaturalConvex (ConvexConjugate f) ∧
          IsIntegerValued (ConvexConjugate f) ∧
          ConvexConjugate (ConvexConjugate f) = f) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, DiscreteConvex.LConvexFunctions.LNaturalConvex g →
        IsIntegerValued g →
        DiscreteConvex.MConvexFunctions.MNaturalConvex (ConvexConjugate g) ∧
          IsIntegerValued (ConvexConjugate g) ∧
          ConvexConjugate (ConvexConjugate g) = g) := by sorry

end DiscreteConvex.ConjugacyDuality
