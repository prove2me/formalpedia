-- Prove2me | Theorems.Thm_AlgebraicPCSP_OneInThree_lemma_8_7
-- name    : AlgebraicPCSP.OneInThree.lemma_8_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:25.605093+00:00
-- url     : https://prove2.me/theorems/80f4b09b-f0f0-46ef-8c42-4d52149cee4a
-- title:
--   Lemma 8.7 — the three matrices of a cover are not all g-equivalent
-- statement:
--   Let $D$ be a set, $R\subseteq D^3$, $f:\{0,1\}\to D$ a homomorphism from $\mathbf T$ (1-in-3) to $(D;R)$, and $g:D\to\{0,1\}$ a homomorphism from $(D;R)$ to $\mathbf H_2$ (not-all-equal). Let $s:D^p\to D$ be a polymorphism of $(D;R)$ and $t$ the $p^2$-ary operation built from $s$. If $X,Y,Z$ is a cover of zero-one $p\times p$ matrices, then
--   $$\neg\,(X\sim Y\ \wedge\ Y\sim Z),$$
--   that is, $X,Y,Z$ are not all $g$-equivalent.
--
--   This is the single place where the polymorphism and the two homomorphisms enter the combinatorics of §8; every later lemma derives its non-equivalences from it.
--
--   **Formalization Note** Neither primality of $p$ nor finiteness of $D$ nor cyclicity of $s$ is used by the lemma, so they are not assumed.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 54, Lemma 8.7

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices

namespace AlgebraicPCSP.OneInThree

open PCSPBLPAff.Symmetric

/-- Lemma 8.7 (p. 54): if `X, Y, Z` is a cover, then `X, Y, Z` are not all `g`-equivalent.
Here `s` is a polymorphism of `(D; R)`, `f : T → (D; R)` and `g : (D; R) → H₂` are
homomorphisms, and zero-one matrices are evaluated through `f`. -/
theorem lemma_8_7 {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (X Y Z : Fin p → Fin p → Fin 2) (hcover : IsCover X Y Z) :
    ¬ (GEquiv f g s X Y ∧ GEquiv f g s Y Z) := by sorry

end AlgebraicPCSP.OneInThree
