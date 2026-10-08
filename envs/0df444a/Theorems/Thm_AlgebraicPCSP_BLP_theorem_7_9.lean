-- Prove2me | Theorems.Thm_AlgebraicPCSP_BLP_theorem_7_9
-- name    : AlgebraicPCSP.BLP.theorem_7_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:40.226415+00:00
-- url     : https://prove2.me/theorems/a43866fd-1bb6-43aa-8576-4e56ad284bef
-- title:
--   Theorem 7.9 — BLP solves PCSP(A, B) iff Pol(A, B) has symmetric functions of all arities iff 𝒬_conv → Pol(A, B) iff (A, B) is pp-constructible from a finite reduct of Q_conv
-- statement:
--   Let $(\mathbf A,\mathbf B)$ be a PCSP template: two finite relational structures over the same finite signature, all arities at least $1$, with a homomorphism $\mathbf A\to\mathbf B$ and nonempty domain $B$. The following are equivalent.
--
--   1. BLP solves $\mathrm{PCSP}(\mathbf A,\mathbf B)$: every instance $\mathbf I$ with $\mathrm{BLP}_{\mathbf A}(\mathbf I)=1$ maps homomorphically to $\mathbf B$.
--   2. $\mathrm{Pol}(\mathbf A,\mathbf B)$ contains symmetric functions of all arities: for every $n\ge 1$ there is a polymorphism $f:A^n\to B$ with $f(x_{\pi(1)},\dots,x_{\pi(n)})=f(x_1,\dots,x_n)$ for all permutations $\pi$ of $[n]$.
--   3. $\mathrm{Pol}(\mathbf A,\mathbf B)$ admits a minion homomorphism from $\mathcal Q_{\mathrm{conv}}$, the minion of convex linear functions $\sum_i\alpha_ix_i$ ($\alpha_i\in[0,1]$, $\sum_i\alpha_i=1$) on $\mathbb Q$:
--   $$\mathcal Q_{\mathrm{conv}}\longrightarrow\mathrm{Pol}(\mathbf A,\mathbf B).$$
--   4. $(\mathbf A,\mathbf B)$ is pp-constructible from $(\mathbf D,\mathbf D)$ for some finite reduct $\mathbf D$ of $\mathbf Q_{\mathrm{conv}}$, the structure on $\mathbb Q$ whose relations are the rational linear inequalities.
--
--   The theorem characterises the PCSP templates for which the basic linear programming relaxation is a correct decision procedure, in three algebraic ways; it generalises Theorem 2(5)&(6) of Kun, O'Donnell, Tamaki, Yoshida and Zhou from CSPs to promise CSPs.
--
--   **Formalization Note** The conclusion is a `List.TFAE` of the four items. Item (1) uses `BLPSolves`, where $\mathrm{BLP}_{\mathbf A}(\mathbf I)=1$ is the feasibility of the basic LP with $\mu_{\mathbf v,R}$ vanishing off $R^{\mathbf A}$ (the paper's remark after Definition 7.7). Item (4) uses pp-constructibility over possibly infinite domains, starting from `QconvReduct S` for a finite set `S` of non-strict rational inequalities. Nonemptiness of $B$ excludes exactly the degenerate template $A=B=\emptyset$ (a homomorphism $\mathbf A\to\mathbf B$ forces $A=\emptyset$ when $B=\emptyset$): there items (1)–(3) hold while no pp-construction from a structure on $\mathbb Q$ reaches an empty $B$, so the printed theorem fails. For $A=\emptyset\ne B$ all four items hold, so the weaker hypothesis on $B$ is used rather than nonemptiness of $A$.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 46, Theorem 7.9

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_BLP_PPConstruction
import Definitions.Def_AlgebraicPCSP_BLP_Qconv
import Definitions.Def_AlgebraicPCSP_BLP_LP

namespace AlgebraicPCSP.BLP

open PCSPBLPAff.Symmetric

/-- Theorem 7.9 (arXiv:1811.00970v3, p. 46). Let `(𝔸, 𝔹)` be a PCSP template (finite signature,
arities `≥ 1`, finite domains, `B` nonempty). The following are equivalent:
1. BLP solves `PCSP(𝔸, 𝔹)`;
2. `Pol(𝔸, 𝔹)` contains symmetric functions of all arities `n ≥ 1`;
3. there is a minion homomorphism `𝒬_conv → AlgebraicPCSP.Theory.Pol(𝔸, 𝔹)`;
4. `(𝔸, 𝔹)` is pp-constructible from `(D, D)` for some finite reduct `D` of `Q_conv`. -/
theorem theorem_7_9 {τ : Type} [Fintype τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (h : IsPromiseTemplate 𝔸 𝔹) :
    List.TFAE
      [BLPSolves 𝔸 𝔹,
       ∀ n : ℕ, 0 < n → ∃ f : (Fin n → A) → B, IsPolymorphism 𝔸 𝔹 f ∧ IsSymmetric f,
       ∃ ξ, AlgebraicPCSP.Theory.IsMinionHom convexMinion (AlgebraicPCSP.Theory.Pol 𝔸 𝔹 h) ξ,
       ∃ S : Finset LinIneq,
         PPConstructible (Template.of (QconvReduct S) (QconvReduct S) (fun ι => ι.val.k_pos))
           (Template.of 𝔸 𝔹 har)] := by sorry

end AlgebraicPCSP.BLP
