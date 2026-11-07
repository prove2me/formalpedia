-- Prove2me | Theorems.Thm_CopylessCRA_ccra_rational
-- name    : CopylessCRA.ccra_rational
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:22.977509+00:00
-- url     : https://prove2.me/theorems/495a2514-4e3a-49aa-a80b-6415af636606
-- title:
--   §2.1, p.6 — every CCRA computes a rational series, via its linearization on $\bigoplus_s V_r$
-- statement:
--   Let $\mathcal C$ be a CCRA with control states $S$, registers $x_1,\dots,x_r$, updates $P_{s,a}$ and outputs $\omega_s$, computing $f$. Let $V_r$ be the multiaffine polynomials and $B_P(h)=h\circ P$ the pullback. Define on $\bigoplus_{s\in S}V_r$
--   $$(B_ah)_s=h_{\delta(s,a)}\circ P_{s,a},\qquad \lambda(h)=h_{s_0}(x^{(0)}),\qquad o=(\omega_s)_s .$$
--   Then:
--
--   1. each $B_a$ maps $\bigoplus_sV_r$ into itself;
--   2. for every word $w=a_1\cdots a_n$, $f(w)=\lambda B_{a_1}\cdots B_{a_n}o$;
--   3. $B_{P\circ P'}=B_{P'}B_P$ for copyless maps $P,P'$;
--   4. $f$ has a finite-dimensional linear representation, i.e. it is a rational series.
--
--   This is the linearization behind "CCRA compute only rational series" and the starting point of the final claim of Theorem 1.
--
--   **Formalization Note** The operators are defined on $S\to\mathbb Q[x_1,\dots,x_r]$ and clause 1 says they restrict to $\bigoplus_sV_r$.
--
--   Differences from the source:
--   - encoding: operators $B_a$ on $\bigoplus_s V_r$ → operators on $S\to\mathbb Q[x]$ together with the invariance of $(V_r)^S$ (clause 1); reason: the restriction to the invariant subspace is the paper's operator; same instances
--   - generalization: copyless maps given by syntactic copyless tuples (§2.1) → maps with multiaffine coordinates and pairwise disjoint variable supports (`IsCopylessMap`); reason: every syntactic copyless tuple is such a map (proved in `Solutions/verification/CopylessCRA_syntactic.lean`), so the statement specializes to the paper's
--   - encoding: "computes a rational series" → existence of a matrix representation $f(w)=\lambda M_w\gamma$ on some $\mathbb Q^d$; reason: the definition of a rational series
--   - generalization: words over a (finite) alphabet $\Sigma$ → words over any type $\alpha$ of letters (no finiteness assumed); reason: the linearization is defined letter by letter and never uses finiteness of the alphabet; a finite alphabet is a special case
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), §2.1, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_CopylessCRA_CCRA
import Definitions.Def_CopylessCRA_IsRep
import Definitions.Def_CopylessCRA_IsCopylessMap

namespace CopylessCRA

/-- **Linearization of a CCRA (§2.1).** For a copyless map `P`, the pullback `B_P(h) = h ∘ P` preserves
`V_r`; `B_{P∘P′} = B_{P′} B_P`; and every CCRA computes a rational series: on `⊕_{s ∈ S} V_r` let
`(B_a h)_s = h_{δ(s,a)} ∘ P_{s,a}`, `λ(h) = h_{s0}(x(0))` and `o = (ω_s)_s`; then
`f(w) = λ B_{a₁} ⋯ B_{aₙ} o`.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), §2.1, p.6 (PDF p.8).

**Formalization Note** The operators `B_a` are defined on `S → ℚ[x₁,…,x_r]`; the first clause says
`(V_r)^S` is invariant under each of them, so they restrict to the paper's operators on `⊕_s V_r`.
The composition clause is stated for copyless maps in the semantic sense (`IsCopylessMap`). The last
clause ("computes a rational series") gives a finite-dimensional matrix representation. -/
theorem ccra_rational {α : Type*} (C : CCRA α) :
    (∀ (a : α) (h : C.S → MvPolynomial (Fin C.r) ℚ), (∀ s, h s ∈ multiaffine C.r) →
        ∀ s, C.linOp a h s ∈ multiaffine C.r) ∧
    (∀ w : List α, C.eval w = C.linInit ((w.map C.linOp).prod C.linOut)) ∧
    (∀ P P' : Fin C.r → MvPolynomial (Fin C.r) ℚ, IsCopylessMap P → IsCopylessMap P' →
        pullback (compMap P P') = pullback P' * pullback P) ∧
    ∃ (d : ℕ) (lam : Fin d → ℚ) (M : α → Matrix (Fin d) (Fin d) ℚ) (γ : Fin d → ℚ),
      IsRep C.eval lam M γ := by sorry

end CopylessCRA
