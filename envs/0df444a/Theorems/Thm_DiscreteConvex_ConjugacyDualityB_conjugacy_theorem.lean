-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_conjugacy_theorem
-- name    : DiscreteConvex.ConjugacyDualityB.conjugacy_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:34:42.422986+00:00
-- url     : https://prove2.me/theorems/72b639f3-1ef8-4511-9d5f-5c98580ca3d8
-- title:
--   Theorem 8.4 -- conjugacy_theorem
-- statement:
--   **Theorem 8.4** (Conjugacy theorem; p.209). GOAL. (1) The classes of polyhedral M-convex functions $M[\mathbb R\to\mathbb R]$ and polyhedral L-convex functions $L[\mathbb R\to\mathbb R]$ are in one-to-one correspondence under the Legendre-Fenchel transform: for $f\in M$ and $g\in L$, $f^\bullet\in L$, $g^\bullet\in M$, $f^{\bullet\bullet}=f$, $g^{\bullet\bullet}=g$. (2) The M$^\natural$/L$^\natural$ analogue.
--
--   The theoretical climax of chapter 8: M-convexity (exchangeability) and L-convexity (submodularity) are not merely analogous discrete convexity notions but are literally dual to each other under the same transform that is self-dual on ordinary convex functions. Mission `10-conjugacy-i` explicitly deferred this theorem, noting it "needs a polyhedral $\mathbb R^V$-domain M-/L-convex-function layer this series has never built" — that layer now exists, built across missions `23`-`24-ch06*-mconvexfunctions` and `26`-`27-ch07*-lconvexfunctions`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.209, Theorem 8.4.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.209, Theorem 8.4

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNaturalConvexR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SBFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_TRFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LNaturalConvexR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateRW
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsPolyhedralConvex

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.4 (Conjugacy theorem; p.209). GOAL. Polyhedral M-convex and L-convex functions are
in one-to-one correspondence under the Legendre-Fenchel transform, both in the plain and the
natural-convexity variants. Polyhedrality is the book's hypothesis and is not implied by the
axioms: `f = 0` on the open segment `{(t, -t) : 0 < t < 1}` and `+∞` elsewhere satisfies
(M-EXC[R]) but `f•• ≠ f`, and `g = 0` on the open strip `{0 < p₁ - p₂ < 1}` satisfies (SBF[R])
and (TRF[R]) with `g•• ≠ g`. -/
theorem conjugacy_theorem :
    (∀ f : (V → ℝ) → WithTop ℝ, IsPolyhedralConvex f → MExchangeAxiomR f →
      SBFR (ConvexConjugateRW f) ∧ TRFR (ConvexConjugateRW f) ∧
        ConvexConjugateRW (ConvexConjugateRW f) = f) ∧
    (∀ g : (V → ℝ) → WithTop ℝ, IsPolyhedralConvex g → (SBFR g ∧ TRFR g) →
      MExchangeAxiomR (ConvexConjugateRW g) ∧
        ConvexConjugateRW (ConvexConjugateRW g) = g) ∧
    (∀ f : (V → ℝ) → WithTop ℝ, IsPolyhedralConvex f → MNaturalConvexR f →
      LNaturalConvexR (ConvexConjugateRW f) ∧ ConvexConjugateRW (ConvexConjugateRW f) = f) ∧
    (∀ g : (V → ℝ) → WithTop ℝ, IsPolyhedralConvex g → LNaturalConvexR g →
      MNaturalConvexR (ConvexConjugateRW g) ∧ ConvexConjugateRW (ConvexConjugateRW g) = g) := by sorry

end DiscreteConvex.ConjugacyDualityB
