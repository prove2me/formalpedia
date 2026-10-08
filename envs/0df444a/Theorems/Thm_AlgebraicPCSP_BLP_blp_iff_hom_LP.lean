-- Prove2me | Theorems.Thm_AlgebraicPCSP_BLP_blp_iff_hom_LP
-- name    : AlgebraicPCSP.BLP.blp_iff_hom_LP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:16.145954+00:00
-- url     : https://prove2.me/theorems/47948254-1bd0-458f-81b2-317af3a5cbda
-- title:
--   §7.2, p. 47 — BLP_A(I) = 1 iff I maps homomorphically to LP(A)
-- statement:
--   Let $\mathbf A$ be a finite relational structure and $\mathbf I$ an instance over the same signature. Then
--   $$\mathrm{BLP}_{\mathbf A}(\mathbf I)=1\iff \mathbf I\to\mathrm{LP}(\mathbf A),$$
--   where $\mathrm{BLP}_{\mathbf A}(\mathbf I)=1$ means that the basic LP relaxation (7.1)–(7.2), with $\mu_{\mathbf v,R}$ vanishing off $R^{\mathbf A}$, has a rational solution, and $\mathrm{LP}(\mathbf A)$ is the structure of rational probability distributions of Definition 7.10.
--
--   This is the observation that connects the algorithmic condition in item (1) of Theorem 7.9 to a single homomorphism problem: BLP solves $\mathrm{PCSP}(\mathbf A,\mathbf B)$ iff every finite structure that maps to $\mathrm{LP}(\mathbf A)$ maps to $\mathbf B$.
--
--   **Formalization Note** The instance is the referenced `Instance`, and "$\mathbf I$ maps to $\mathrm{LP}(\mathbf A)$" is `SatIn X (LP 𝔸)`: an assignment of distributions to the variables sending every constraint tuple into the corresponding relation of $\mathrm{LP}(\mathbf A)$. No finiteness of the signature is needed.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 47, §7.2, sentence after Definition 7.10 ("I is an instance such that BLP_A(I) = 1 if and only if I maps homomorphically to LP(A)")

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_BLP_LP

namespace AlgebraicPCSP.BLP

open PCSPBLPAff.Symmetric

/-- §7.2, p. 47 (arXiv:1811.00970v3): an instance `I` has `BLP_𝔸(I) = 1` iff `I` maps
homomorphically to `LP(𝔸)`. `BLP_𝔸(I) = 1` is the feasibility of the basic LP relaxation with
`µ_{v,R}` vanishing off `R^𝔸` (the remark after Definition 7.7, p. 45), i.e. `IsLPSol`; the
instance maps to `LP(𝔸)` iff it is satisfiable in `LP(𝔸)`. -/
theorem blp_iff_hom_LP {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (X : Instance τ ar) :
    (∃ w p, IsLPSol X 𝔸 w p) ↔ SatIn X (LP 𝔸) := by sorry

end AlgebraicPCSP.BLP
