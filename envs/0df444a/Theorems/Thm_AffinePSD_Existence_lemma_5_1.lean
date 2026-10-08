-- Prove2me | Theorems.Thm_AffinePSD_Existence_lemma_5_1
-- name    : AffinePSD.Existence.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:27.335441+00:00
-- url     : https://prove2.me/theorems/d6504e67-3e1b-46df-800d-e43404df7017
-- title:
--   Lemma 5.1 — R is analytic on S_d^{++} and quasi-monotone increasing on S_d^+
-- statement:
--   Let $(\alpha,b,\beta^{ij},c,\gamma,m,\mu)$ satisfy every condition of Definition 2.3 except possibly the drift condition (2.4), and let $R$ be the function (2.17). Then:
--   1. $R$ is real analytic on $S_d^{++}$;
--   2. $R$ is quasi-monotone increasing on $S_d^+$: for $u,v,x\in S_d^+$ with $u\preceq v$ and $\langle u,x\rangle=\langle v,x\rangle$,
--   $$\langle R(u),x\rangle\le\langle R(v),x\rangle;$$
--   3. the integrands defining $F(u)$ and $R(u)$ are integrable for every $u\in S_d^+$.
--
--   This is the input to the comparison argument for the Riccati equation (2.15). By Remark 5.4, only the admissibility of $\alpha,\beta^{ij},\gamma,\mu$ is used.
--
--   **Formalization Note** The hypothesis omits (2.4), so the statement is stronger than the page, which assumes a full admissible parameter set. Analyticity on the open subset $S_d^{++}$ of $S_d$ is analyticity of $y\mapsto R((y+y^\top)/2)$ on the open set $\{y\in M_d:(y+y^\top)/2\succ0\}$. Item 3 rules out Lean's convention that a non-integrable integral is $0$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 5.1, p. 38 (and Remark 5.4, p. 41)

import Mathlib
import Definitions.Def_AffinePSD_Existence_Params
import Definitions.Def_AffinePSD_Existence_QuasiMono

open MeasureTheory

namespace AffinePSD.Existence

/-- Lemma 5.1 (arXiv:0910.0137v3, §5.1, p. 38): `R` of (2.17) is analytic on `S_d^{++}` and
quasi-monotone increasing on `S_d^+`.
Formalization Note: hypothesis `AdmissibleCore` (Definition 2.3 without the drift condition (2.4)),
which is weaker than the section's standing admissibility; by Remark 5.4 only the admissibility of
`α, β^{ij}, γ, μ` is used. Analyticity on the open subset `S_d^{++}` of `S_d` is encoded as
analyticity of `y ↦ R((y + y^⊤)/2)` on the open set `{y ∈ M_d | (y + y^⊤)/2 ≻ 0}`. The third
conjunct `RiccatiIntegrable` (the integrands of (2.16)–(2.17) are integrable at every
`u ∈ S_d^+`) guards against Lean's junk value of a non-integrable Bochner integral; it is stronger
than the page and true. -/
theorem lemma_5_1 {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) (hP : AffinePSD.Necessity.AdmissibleCore χ P) :
    AnalyticOnNhd ℝ (fun y => AffinePSD.Necessity.Rpar χ P (sym y)) {y | PD (sym y)} ∧
    QuasiMonoOn (AffinePSD.Necessity.Rpar χ P) {u | PSD u} ∧ RiccatiIntegrable χ P := by sorry

end AffinePSD.Existence
