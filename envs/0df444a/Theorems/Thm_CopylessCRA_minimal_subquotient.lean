-- Prove2me | Theorems.Thm_CopylessCRA_minimal_subquotient
-- name    : CopylessCRA.minimal_subquotient
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:38.272083+00:00
-- url     : https://prove2.me/theorems/2cfb6e6c-651e-44a4-bfae-8daa234a3107
-- title:
--   §2.2, display (2), p.6 — the minimal representation is an invariant subquotient of every representation
-- statement:
--   Let $(\lambda',M',\gamma')$ be a representation of $f$ on $\mathbb Q^\iota$ and put
--   $$W=\operatorname{span}\{M'_w\gamma':w\in\Sigma^*\},\qquad N=\{h\in W:\lambda'M'_vh=0\text{ for all }v\in\Sigma^*\}.\tag{2}$$
--   Let $(\lambda,M,\gamma)$ be a minimal representation of $f$ on $\mathbb Q^d$. Then:
--
--   1. $W$ and $N$ are invariant under every $M'_a$;
--   2. there is a linear isomorphism $W/N\cong\mathbb Q^d$ sending the class of $M'_w\gamma'$ to $M_w\gamma$, intertwining the operator induced by $M'_a$ with $M_a$ for every $a$, and carrying the functional induced by $\lambda'$ to $\lambda$;
--   3. if all $M'_a$ are invertible, then so are all $M_a$.
--
--   This is how invertibility passes from a machine's linearization to the minimal representation (final claim of Theorem 1).
--
--   Differences from the source:
--   - encoding: a representation on an arbitrary space $X$ → a representation on $\mathbb Q^\iota$ for a finite type $\iota$; reason: every finite-dimensional space is isomorphic to some $\mathbb Q^\iota$; the paper's representations are finite-dimensional
--   - encoding: "the induced representation on $W/N$ is isomorphic to every minimal representation" → an explicit isomorphism given on the classes of $M'_w\gamma'$, intertwining letter operators and matching $\lambda$; reason: this is the meaning of an isomorphism of representations
--   - generalization: words over a (finite) alphabet $\Sigma$ → words over any type $\alpha$ of letters (no finiteness assumed); reason: the argument is linear algebra on the finite-dimensional spaces $W$, $N$, $\mathbb Q^d$ and never uses finiteness of the alphabet; a finite alphabet is a special case
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), §2.2, display (2), p.6 (PDF p.8)

import Mathlib
import Definitions.Def_CopylessCRA_IsRep
open Matrix

namespace CopylessCRA

/-- **The minimal representation is an invariant subquotient of every representation (§2.2).**
For an arbitrary representation `(λ', M', γ')` of `f` put `W = span{M'_w γ' : w ∈ Σ*}` and
`N = {h ∈ W : λ' M'_v h = 0 for all v ∈ Σ*}` (display (2)). Both are invariant, the induced
representation on `W/N` is isomorphic to every minimal representation `(λ, M, γ)` of `f`, and if all
`M'_a` are invertible then so are the minimal letter matrices.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), §2.2, display (2), p.6 (PDF p.8).

**Formalization Note** The isomorphism `W/N ≅ ℚ^d` sends the class of `M'_w γ'` to `M_w γ`,
intertwines the operators induced by `M'_a` with `M_a`, and matches the functionals induced by `λ'`
with `λ`. The arbitrary representation lives on `ℚ^ι` for a finite type `ι`. -/
theorem minimal_subquotient {α ι : Type*} [Fintype ι] [DecidableEq ι] (f : List α → ℚ)
    (lam' : ι → ℚ) (M' : α → Matrix ι ι ℚ) (γ' : ι → ℚ) (hrep' : IsRep f lam' M' γ')
    {d : ℕ} (lam : Fin d → ℚ) (M : α → Matrix (Fin d) (Fin d) ℚ) (γ : Fin d → ℚ)
    (hrep : IsRep f lam M γ) (hmin : IsMinimalRep lam M γ) :
    ∃ (hW : ∀ a, ∀ h ∈ reachSpan M' γ', Matrix.toLin' (M' a) h ∈ reachSpan M' γ')
      (hN : ∀ a, ∀ h ∈ reachSpan M' γ' ⊓ unobservable lam' M',
        Matrix.toLin' (M' a) h ∈ reachSpan M' γ' ⊓ unobservable lam' M'),
      (∃ e : (reachSpan M' γ' ⧸ (reachSpan M' γ' ⊓ unobservable lam' M').comap
          (reachSpan M' γ').subtype) ≃ₗ[ℚ] (Fin d → ℚ),
        (∀ w : List α, e (Submodule.Quotient.mk
            ⟨wordMat M' w *ᵥ γ', Submodule.subset_span ⟨w, rfl⟩⟩) = wordMat M w *ᵥ γ) ∧
        (∀ a, e.toLinearMap ∘ₗ quotOp (Matrix.toLin' (M' a)) (reachSpan M' γ')
            (reachSpan M' γ' ⊓ unobservable lam' M') (hW a) (hN a) =
          Matrix.toLin' (M a) ∘ₗ e.toLinearMap) ∧
        (∀ h : reachSpan M' γ', lam ⬝ᵥ e (Submodule.Quotient.mk h) = lam' ⬝ᵥ (h : ι → ℚ))) ∧
      ((∀ a, IsUnit (M' a)) → ∀ a, IsUnit (M a)) := by sorry

end CopylessCRA
