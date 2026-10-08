-- Prove2me | Theorems.Thm_AlgebraicPCSP_BLP_remark_7_13
-- name    : AlgebraicPCSP.BLP.remark_7_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:25.080272+00:00
-- url     : https://prove2.me/theorems/5ca22960-1e2d-4529-a8a1-a3f75ebd74d8
-- title:
--   Remark 7.13 — compactness: a countable structure whose finite substructures map to a finite B maps to B
-- statement:
--   Let $\mathbf I$ be a relational structure with a countable (possibly infinite) universe $I$, and let $\mathbf B$ be a similar structure with a finite universe. Suppose that for every finite set $S\subseteq I$, the substructure of $\mathbf I$ on $S$ maps homomorphically to $\mathbf B$. Then
--   $$\mathbf I\to\mathbf B.$$
--
--   In the proof of Theorem 7.9 this turns homomorphisms from the finite pieces of the countable structure $\mathrm{LP}(\mathbf A)$ into a single homomorphism $\mathrm{LP}(\mathbf A)\to\mathbf B$.
--
--   **Formalization Note** A homomorphism from the substructure on $S$ is encoded as a map $I\to B$ required to preserve only the tuples of $\mathbf I$ whose entries all lie in $S$; its values off $S$ are irrelevant. The platform theorem `PCSPBLPAff.Characterization.lemma_16` states the same conclusion without the countability hypothesis.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, pp. 47–48, Remark 7.13

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace AlgebraicPCSP.BLP

open PCSPBLPAff.Symmetric

/-- Remark 7.13 (arXiv:1811.00970v3, pp. 47–48), compactness for countable structures: let `𝕀`
be a structure with a countable (possibly infinite) universe and `𝔹` a similar finite structure.
If every finite substructure of `𝕀` maps homomorphically to `𝔹`, then `𝕀` maps homomorphically
to `𝔹`. A homomorphism from the substructure on a finite set `S` is encoded as a map `I → B`
that is required to preserve only the tuples of `𝕀` with all entries in `S`. -/
theorem remark_7_13 {τ : Type} {ar : τ → ℕ} {I B : Type} [Countable I] [Finite B]
    (𝕀 : RelStruct τ ar I) (𝔹 : RelStruct τ ar B)
    (hfin : ∀ S : Finset I, ∃ σ : I → B,
      ∀ R : τ, ∀ t ∈ 𝕀.rel R, (∀ k, t k ∈ S) → σ ∘ t ∈ 𝔹.rel R) :
    ∃ σ : I → B, IsHom 𝕀 𝔹 σ := by sorry

end AlgebraicPCSP.BLP
