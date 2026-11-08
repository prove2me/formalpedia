-- Prove2me | Theorems.Thm_AsymSpecConn_corollary_2_11
-- name    : AsymSpecConn.corollary_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:12.377057+00:00
-- url     : https://prove2.me/theorems/356de14b-5a4a-4d9e-a8b7-afb5bbe7b386
-- title:
--   Corollary 2.11 — value sets $\Delta(s_1,\dots,s_q)$ are path-connected
-- statement:
--   Let $\mathcal S$ be a Strassen semiring that is $\mathcal A$-decomposable, let $f_1\in\Delta$, and suppose that for every $f_0\in\Delta$ the pair $f_0,f_1$ has the $\mathcal A$-cover property. Let $s_1,\dots,s_q\in\mathcal S$ and
--   $$\Delta(s_1,\dots,s_q)=\{(g(s_1),\dots,g(s_q)):g\in\Delta\}\subseteq\mathbb R^q.$$
--   Then every point of $\Delta(s_1,\dots,s_q)$ is joined by a path inside this set to $(f_1(s_1),\dots,f_1(s_q))$. In particular $\Delta(s_1,\dots,s_q)$ is path-connected, and for every $s\in\mathcal S$ the set $\Delta(s)\subseteq\mathbb R$ is a closed interval.
--
--   This is the consequence of the interpolation theorem for finitely many coordinates of the spectrum.
--
--   Differences from the source:
--
--   - encoding: closed interval → ∃ a b, a ≤ b and the whole value set equals Set.Icc a b; reason: the standard rendering of a nonempty closed interval, possibly a point
--   - encoding: joined by a path → JoinedIn the value set; reason: the source's proof gives a path in Δ(s_1,…,s_q), and this is the reading of p.18
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Corollary 2.11, p.18

import Mathlib
import Definitions.Def_AsymSpecConn_IsStrassenSemiring
import Definitions.Def_AsymSpecConn_Spectrum
import Definitions.Def_AsymSpecConn_IsADecomposable
import Definitions.Def_AsymSpecConn_HasACoverProperty
import Definitions.Def_AsymSpecConn_interp

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn

/-- **Corollary 2.11** (p.18 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): "Fix f1 ∈ ∆. Suppose S is
A-decomposable and that for every f0 ∈ ∆ the pair f0, f1 has the A-cover property. Let
s1, …, sq ∈ S and ∆(s1, …, sq) := {(g(s1), …, g(sq)) : g ∈ ∆} ⊆ Rq. Then every point of
∆(s1, …, sq) is joined by a path to (f1(s1), …, f1(sq)). In particular ∆(s1, …, sq) is
path-connected, and for every s ∈ S, ∆(s) ⊆ R is a closed interval."

**Formalization Note** "Joined by a path" is a path inside `Δ(s₁, …, s_q)` (`JoinedIn`).
"Closed interval" is `[a, b]` with `a ≤ b` (possibly a point), equal to the whole set `Δ(s)`.
`S` is a Strassen semiring (standing assumption of §2, p.12). -/
theorem corollary_2_11 {S : Type*} [CommSemiring S] (P : Preorder S)
    (hS : IsStrassenSemiring S P) (A : Set S) (hA : IsADecomposable P A)
    (f₁ : ↥(Spectrum S P)) (hcov : ∀ f₀ : ↥(Spectrum S P), HasACoverProperty P A ![f₀, f₁])
    {q : ℕ} (s : Fin q → S) :
    (∀ x ∈ valueSet S P s, JoinedIn (valueSet S P s) x (fun j => ((f₁.1 (s j) : ℝ≥0) : ℝ))) ∧
    IsPathConnected (valueSet S P s) ∧
    (∀ s₀ : S, ∃ a b : ℝ, a ≤ b ∧
      Set.range (fun g : ↥(Spectrum S P) => ((g.1 s₀ : ℝ≥0) : ℝ)) = Set.Icc a b) := by sorry

end AsymSpecConn
