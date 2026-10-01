-- Prove2me | Theorems.Thm_FoundationsML_Kernels_RKHS_exists
-- name    : FoundationsML.Kernels.RKHS_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:00:12.163869+00:00
-- url     : https://prove2.me/theorems/55340e55-cc8e-46fb-8e83-7418e34756bd
-- title:
--   Theorem 6.8 — reproducing kernel Hilbert space (RKHS)
-- statement:
--   **Statement (Theorem 6.8, p. 110, PDF p. 127).** Let $K:X\times X\to\mathbb R$ be a PDS
--   kernel. Then there exists a Hilbert space $H$ and a mapping $\Phi:X\to H$ such that
--   $K(x,x')=\langle\Phi(x),\Phi(x')\rangle$ for all $x,x'\in X$, and $H$ has the reproducing
--   property $h(x)=\langle h,K(x,\cdot)\rangle$ for all $h\in H$, $x\in X$. $H$ is called a
--   reproducing kernel Hilbert space (RKHS) associated to $K$.
--
--   This is the chapter's central structural result: every PDS kernel implicitly defines an
--   inner product (and hence a feature space), which is what makes kernel methods work without
--   ever having to compute a feature map explicitly.
--
--   **Formalization Note.** `X` is a plain `Type` (not `Type*`), avoiding universe-polymorphic
--   existential quantification over the constructed Hilbert space's own type — a harmless
--   simplification, since every application in this book instantiates `X` at a concrete, small
--   type. The conclusion is packaged as `IsRKHSOf K Φ ev`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 110, Theorem 6.8 (PDF p. 127)

import Mathlib
import Definitions.Def_FoundationsML_Kernels_IsPDS
import Definitions.Def_FoundationsML_Kernels_IsRKHSOf

namespace FoundationsML.Kernels

/-- Theorem 6.8 (Reproducing kernel Hilbert space (RKHS); Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 110, PDF p. 127). Let
`K : X × X → ℝ` be a PDS kernel. Then there exists a Hilbert space `H` and a mapping `Φ` from
`X` to `H` such that `K(x,x') = ⟨Φ(x),Φ(x')⟩` for all `x,x' ∈ X`, and `H` has the reproducing
property `h(x) = ⟨h, K(x,·)⟩` for all `h ∈ H`, `x ∈ X`. `H` is called the RKHS associated to
`K`.

**Formalization Note.** `X` is a plain `Type` (not `Type*`), avoiding universe-polymorphic
existential quantification over the constructed Hilbert space's own type; a harmless
simplification (every application in this book instantiates `X` at a concrete, small type). -/
theorem RKHS_exists {X : Type} (K : X → X → ℝ) (hK : IsPDS K) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (Φ : X → H) (ev : H → X → ℝ), IsRKHSOf K Φ ev := by sorry

end FoundationsML.Kernels
