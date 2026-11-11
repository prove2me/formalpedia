-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_theorem_F_5_2
-- name    : BlockOrthoCSP.Decide.theorem_F_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:12:27.904631+00:00
-- url     : https://prove2.me/theorems/96041a4d-e2e9-47f6-8304-d94d099ad0be
-- title:
--   Theorem F.5.2 — pinned constraint-function isomorphism: equal pinned partition values on all labelled instances iff a domain isomorphism matching the pins up to twins
-- statement:
--   Let $\mathcal H$ and $\mathcal G$ be similar finite families of constraint functions (of any arities, nullary ones included) over finite domains $D_{\mathcal H}$, $D_{\mathcal G}$ and a field $L$ of characteristic zero. Fix $k \ge 1$ and pins $\beta : [k] \to D_{\mathcal H}$, $\gamma : [k] \to D_{\mathcal G}$. Then
--   $$Z^{\mathcal H}_\beta(I) = Z^{\mathcal G}_\gamma(I_{\mathcal H\to\mathcal G}) \text{ for every } k\text{-labelled } \mathcal H\text{-instance } I$$
--   if and only if $|D_{\mathcal H}| = |D_{\mathcal G}|$ and there is an isomorphism $\sigma : D_{\mathcal H} \to D_{\mathcal G}$ of the families with $\sigma(\beta(i))$ and $\gamma(i)$ twins in $\mathcal G$ for every $i \in [k]$. The labelled instances are arbitrary: repeated constraints, repeated scope variables and any number of unlabelled variables are allowed (restricting to simple instances makes the statement false, Remark F.B.1).
--
--   Differences from the source:
--   - generalization: similar finite SETS H, G of constraint functions with an arity-preserving bijection → two families H, G indexed by one finite type ι with common arities ar (repetitions allowed); reason: a pair of similar sets is the case ι = H with G composed with the bijection; the proof never uses that the functions are distinct
--   - generalization: constraint functions of arity r ≥ 1 (§F.2.2) → arities ar i arbitrary, nullary functions allowed; reason: a nullary pair is forced equal by the one-constraint instance, every instance without nullary constraints is an instance of the subfamily of arity ≥ 1, and twins impose nothing on nullary functions, so the statement reduces to the paper's theorem for that subfamily
--   - encoding: a k-labelled instance with k distinct labelled variables and unlabelled ones → FamInst ar k: variables Fin (k + h), the first k labelled; reason: every labelled instance is of this form after renaming variables, which changes no pinned value
--   - encoding: 'Conversely, such a domain bijection and twin replacements preserve pinned partition values on every k-labelled instance' → the reverse implication of the stated ↔; reason: the same statement
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-20, Theorem F.5.2

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Pinned

namespace BlockOrthoCSP.Decide

/-- Theorem F.5.2 (pinned constraint-function isomorphism), p. F-20, both directions. The
similar families are `H` and `G`, indexed by the same finite `ι` with the same arities. -/
theorem theorem_F_5_2 {ι : Type} [Fintype ι] (ar : ι → ℕ)
    {DH DG L : Type} [Fintype DH] [Fintype DG] [Field L] [CharZero L]
    (H : (i : ι) → (Fin (ar i) → DH) → L) (G : (i : ι) → (Fin (ar i) → DG) → L)
    (k : ℕ) (hk : 1 ≤ k) (β : Fin k → DH) (γ : Fin k → DG) :
    (∀ I : FamInst ar k, pinnedValue H I β = pinnedValue G I γ) ↔
      (Fintype.card DH = Fintype.card DG ∧
        ∃ σ : DH ≃ DG, IsFamilyIso H G σ ∧ ∀ l : Fin k, AreTwins G (σ (β l)) (γ l)) := by sorry

end BlockOrthoCSP.Decide
