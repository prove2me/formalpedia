-- Prove2me | Theorems.Thm_ConservativeAD_AutoDiff_theorem_8
-- name    : ConservativeAD.AutoDiff.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:37.190445+00:00
-- url     : https://prove2.me/theorems/13b243ae-589d-465d-82bc-5df5c9175326
-- title:
--   Theorem 8 — forward and reverse mode automatic differentiation are conservative fields for $f$
-- statement:
--   Let $f:\mathbb R^p\to\mathbb R$ be given by an evaluation program (Algorithm 1) with elementary functions $g_k$, $k=p+1,\dots,q$, and suppose that for every non-input node $k$
--
--   1. $D_k:\mathbb R^{|\mathtt{parents}(k)|}\rightrightarrows\mathbb R^{|\mathtt{parents}(k)|}$ is a conservative field for $g_k$ (property (d)), and
--   2. $D_k$ is locally bounded.
--
--   For $x\in\mathbb R^p$ let $D_{\mathrm{fwd}}(x)$ be the set of outputs of Algorithm 2 (forward mode), and $D_{\mathrm{rev}}(x)$ the set of outputs of Algorithm 3 (reverse mode), over all choices $d_k\in D_k(x_{\mathtt{parents}(k)})$, $k=p+1,\dots,q$. Then
--
--   $$
--   D_{\mathrm{fwd}}\ \text{and}\ D_{\mathrm{rev}}:\mathbb R^p\rightrightarrows\mathbb R^p\ \text{are conservative fields for } f .
--   $$
--
--   Nonsmooth automatic differentiation, in either mode, therefore returns an element of a conservative field of the function it differentiates, even where that element is not a Clarke subgradient. This is the result that justifies using backpropagation outputs in nonsmooth first-order methods.
--
--   **Formalization Note** "Conservative field for $f$" is Definition 2 in full: closed graph, nonempty compact values, vanishing circulation and the potential identity. **Hypothesis 2 is added.** The paper obtains local boundedness of the $D_k$ from Remark 3(d) ("From [15, Lemma 3], $D$ is locally bounded"), but a conservative field need not be locally bounded, and without it the conclusion fails: on $\mathbb R$, $D_a(1/m)=\{0,c\sqrt{m/2}\}$ ($m\ge1$) and $D_a(y)=\{0\}$ otherwise is a conservative field for $g_a\equiv0$, and the program $x_2=x_1^2/2$ (with $D_b(y)=\{y\}$), $x_3=g_a(x_2)$ gives $D_{\mathrm{fwd}}(\sqrt{2/m})\ni c$ while $D_{\mathrm{fwd}}(0)=\{0\}$, so the graph of $D_{\mathrm{fwd}}$ is not closed. Algorithm 3 uses the accumulating update $v[j]:=v[j]+v[t]d_{tj}$ (the printed update "$v[j]:=v[t]d_{tj}$" is an overwrite; see the program definition), and the loop bound "$P$" in Algorithm 2 and in (i) is read as $q$. Nodes are 0-based in Lean.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), pp. 21–22, Theorem 8 (i)–(ii)

import Mathlib
import Definitions.Def_ConservativeAD_AutoDiff_ConservativeField
import Definitions.Def_ConservativeAD_AutoDiff_Program

namespace ConservativeAD.AutoDiff

/-- Theorem 8 (forward and backward autodiff are conservative fields), pp. 21–22. Let `f` be given
by an evaluation program (Algorithm 1) whose elementary functions `g_k` admit conservative fields
`D_k` (property (d)), each locally bounded (added; see the natural-language statement). Then the
set-valued maps `x ↦ {outputs of Algorithm 2 over all admissible choices}` and
`x ↦ {outputs of Algorithm 3 over all admissible choices}` are conservative fields for `f`. -/
theorem theorem_8 {p q : ℕ} (P : Program p q)
    (hd : ∀ k : Fin q, p ≤ k.val → ConservativeAD.GradAE.IsPotential (P.D k) (P.g k))
    (hlb : ∀ k : Fin q, p ≤ k.val → IsLocallyBounded (P.D k)) :
    ConservativeAD.GradAE.IsPotential P.Dfwd P.fn ∧ ConservativeAD.GradAE.IsPotential P.Drev P.fn := by sorry

end ConservativeAD.AutoDiff
