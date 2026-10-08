-- Prove2me | Theorems.Thm_AlgebraicPCSP_Theory_corollary_4_10
-- name    : AlgebraicPCSP.Theory.corollary_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:35.397738+00:00
-- url     : https://prove2.me/theorems/0cfda2ad-77a4-4d5b-ba28-de1ec35b519b
-- title:
--   Corollary 4.10 — pp-constructibility gives a minion homomorphism Pol(A, B) → Pol(A′, B′)
-- statement:
--   Let $(\mathbf A,\mathbf B)$ and $(\mathbf A',\mathbf B')$ be PCSP templates of finite structures (finite signatures, arities $\ge1$, nonempty finite domains). If $(\mathbf A',\mathbf B')$ is pp-constructible from $(\mathbf A,\mathbf B)$, then there is a minion homomorphism
--   $$\mathrm{Pol}(\mathbf A,\mathbf B)\to\mathrm{Pol}(\mathbf A',\mathbf B').$$
--
--   This is the step (6) ⇒ (1) of Theorem 4.12.
--
--   **Formalization Note** Templates are bundled (`Template`) because the signature and the domains change along a pp-construction.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 26, Corollary 4.10

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

open PCSPBLPAff.Symmetric

namespace AlgebraicPCSP.Theory

/-- Corollary 4.10 (arXiv:1811.00970v3, p. 26). If the PCSP template `T'` is pp-constructible from
the PCSP template `T`, then there is a minion homomorphism from `Pol(T.𝔸, T.𝔹)` to
`Pol(T'.𝔸, T'.𝔹)`. -/
theorem corollary_4_10 (T T' : Template) (hT : IsPromiseTemplate T.𝔸 T.𝔹)
    (hT' : IsPromiseTemplate T'.𝔸 T'.𝔹) (hc : PPConstructible T T') :
    ∃ ξ, IsMinionHom (Pol T.𝔸 T.𝔹 hT) (Pol T'.𝔸 T'.𝔹 hT') ξ := by sorry

end AlgebraicPCSP.Theory
