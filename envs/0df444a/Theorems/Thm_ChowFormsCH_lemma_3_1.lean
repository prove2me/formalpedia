-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_3_1
-- name    : ChowFormsCH.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:43.747533+00:00
-- url     : https://prove2.me/theorems/30d179c6-d6ab-4959-a554-610e46fada22
-- title:
--   Lemma 3.1 — the Chow form of $\phi(V)$ is the monic substitution $u_{i,j}\mapsto\sum_k u'_{i,k}M_{k,j}$ in $C_V$
-- statement:
--   Let $K$ be algebraically closed, $M\in K^{(n+1)\times(n+1)}$ invertible, $\phi(\alpha)=M\alpha$, and $V\subseteq\mathbb P^n$ an equidimensional projective variety of dimension $r$ with Chow form $C_V$. Let $C'$ be obtained from $C_V$ by the substitution
--   $$
--   u_{i,j}\ \longmapsto\ u'_{i,0}M_{0,j}+u'_{i,1}M_{1,j}+\dots+u'_{i,n}M_{n,j}.
--   $$
--   Then $C'$ divided by its lexicographic leading coefficient is the Chow form of $\phi(V)$.
--
--   The lemma transports Chow forms through the random change of coordinates of Lemma 4.8 in the proof of Theorem 4.9.
--
--   **Formalization Note** "Making the result monic" is dividing by the leading coefficient in the lexicographic order of the Chow-form normalization; the new variables $u'_{i,k}$ are again indexed by $(i,k)$.
--
--   Differences from the source:
--   - encoding: making the result monic → multiplying by the inverse of the lexicographic leading coefficient (chowLeadCoeff); reason: monic means leading coefficient 1 in the paper's lexicographic normalization of Chow forms (§3.1)
--   - encoding: an equidimensional variety V ⊆ P^n → a projective variety V, equidimensional of dimension r (the number of variable groups of C_V); reason: the Chow form of V lives in dim V + 1 groups of variables
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 3.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ChowFormsCH_comps
import Definitions.Def_ChowFormsCH_IsChowForm

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 3.1** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.22). Let `M ∈ K^{(n+1)×(n+1)}`
be invertible, `ϕ(α) = Mα`, and `V ⊆ P^n` an equidimensional variety (of dimension `r`). If `C_V` is
the Chow form of `V`, then the Chow form of `ϕ(V)` is obtained by the substitution
`u_{i,j} ↦ u′_{i,0}M_{0,j} + u′_{i,1}M_{1,j} + ⋯ + u′_{i,n}M_{n,j}` in `C_V` and making the result monic.

**Formalization Note** `K` is algebraically closed. "Making the result monic" is dividing by the
lexicographic leading coefficient (`chowLeadCoeff`), the paper's normalization of Chow forms; the
new variables `u′_{i,k}` are again indexed by `(i, k)`. -/
theorem lemma_3_1 {K : Type} [Field K] [IsAlgClosed K] {n r : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hM : IsUnit M.det)
    (V : Set (ProjSpace n K)) (hV : IsProjVariety V) (hVeq : IsProjEquidim V r)
    (C : MvPolynomial (Fin (r + 1) × Fin (n + 1)) K) (hC : IsNormalizedChowForm V r C) :
    IsNormalizedChowForm (linImage M V) r
      (MvPolynomial.C (chowLeadCoeff (MvPolynomial.aeval (fun ij : Fin (r + 1) × Fin (n + 1) =>
          ∑ k : Fin (n + 1), MvPolynomial.X (ij.1, k) * MvPolynomial.C (M k ij.2)) C))⁻¹ *
        MvPolynomial.aeval (fun ij : Fin (r + 1) × Fin (n + 1) =>
          ∑ k : Fin (n + 1), MvPolynomial.X (ij.1, k) * MvPolynomial.C (M k ij.2)) C) := by sorry

end ChowFormsCH
