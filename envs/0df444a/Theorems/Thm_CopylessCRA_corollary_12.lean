-- Prove2me | Theorems.Thm_CopylessCRA_corollary_12
-- name    : CopylessCRA.corollary_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:32.183505+00:00
-- url     : https://prove2.me/theorems/e8edc3bf-4b26-4ceb-b8e0-01c14504fc4b
-- title:
--   Corollary 12 (One-state constraint), p.9 — the closure of $\rho(\mathcal Y)$ has commuting unipotents and $\mathbb Q$-triangularizable identity component
-- statement:
--   **Standing hypotheses of §3.** $\mathcal Y$ is a monoid acting on $\mathbb Q^r$ by copyless maps $P_y$ with $P_1=\mathrm{id}$ and $P_{yz}=P_z\circ P_y$; its pullbacks $B_y=B_{P_y}$ satisfy $B_{yz}=B_yB_z$. Subspaces $N\subseteq W\subseteq V_r$ are invariant under every $B_y$, $D=W/N$, and $\rho(y)$ is the operator induced by $B_y$ on $D$.
--
--   Assume that $\rho(y)$ is invertible for every $y$ (the hypothesis of Proposition 10), and let $\mathcal H$ be the Zariski closure of $\{\rho(y):y\in\mathcal Y\}$ in $GL(D)$ (over $\overline{\mathbb Q}$). Then any two unipotent elements of $\mathcal H$ commute, and $\mathcal H^\circ$ is triangularizable over $\mathbb Q$.
--
--   Differences from the source:
--   - generalization: copyless maps given by syntactic copyless tuples (§2.1) → maps with multiaffine coordinates and pairwise disjoint variable supports (`IsCopylessMap`); reason: every syntactic copyless tuple is such a map (proved in `Solutions/verification/CopylessCRA_syntactic.lean`), so the statement specializes to the paper's
--   - encoding: $GL(D)$ → $GL_n(\overline{\mathbb Q})$ through an arbitrary rational basis of $D$; the statement is made for every basis; reason: both conclusions are invariant under a rational change of basis
--   - encoding: Zariski closure via polynomials in the entries and $\det^{-1}$ → polynomials in the entries, closed sets taken relative to $GL_d(\overline{\mathbb Q})$; reason: multiplying by a power of $\det$, a unit on $GL$, gives the same closed subsets of $GL$
--   - encoding: identity component $\mathcal G^\circ$ of the algebraic group → the union of all Zariski-connected subsets of $\mathcal G$ containing $1$ (the connected component of $1$); reason: this is the identity component of a linear algebraic group; its group and finite-index properties (A1) are theorems, not definitions
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Corollary 12, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_CopylessCRA_CCRA
import Definitions.Def_CopylessCRA_IsRep
import Definitions.Def_CopylessCRA_IsCopylessMap
import Definitions.Def_CopylessCRA_zariskiClosure

namespace CopylessCRA

/-- **Corollary 12 (One-state constraint).** Under the hypothesis of Proposition 10, let `ℋ` be the
Zariski closure of `{ρ(y) : y ∈ 𝒴}` in `GL(D)`. Then any two unipotent elements of `ℋ` commute, and
`ℋ°` is triangularizable over `ℚ`.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), Corollary 12, p.9 (PDF p.11).

**Formalization Note** The standing hypotheses of §3 (p.8): `𝒴` is a monoid acting by
copyless maps `P_y` with `P_1 = id` and `P_{yz} = P_z ∘ P_y`; `N ⊆ W ⊆ V_r` are invariant under every
`B_y = B_{P_y}`; `D = W/N` and `ρ(y)` is the operator induced by `B_y` (`quotOp`). Copyless maps are
taken in the semantic sense (`IsCopylessMap`), a class containing the syntactic one. `GL(D)` is identified with `GL_n(ℚ̄)` through an arbitrary basis `b`
of `D` over `ℚ` (closure over `ℚ̄`, §2.3); the statement is made for every such basis, and both
conclusions are invariant under the rational change of basis. -/
theorem corollary_12 {r : ℕ} {Y : Type*} [Monoid Y]
    (P : Y → Fin r → MvPolynomial (Fin r) ℚ) (hP : ∀ y, IsCopylessMap (P y))
    (h1 : P 1 = MvPolynomial.X) (hmul : ∀ y z, P (y * z) = compMap (P z) (P y))
    (W N : Submodule ℚ (MvPolynomial (Fin r) ℚ)) (hNW : N ≤ W) (hWV : W ≤ multiaffine r)
    (hW : ∀ y, ∀ h ∈ W, pullback (P y) h ∈ W) (hN : ∀ y, ∀ h ∈ N, pullback (P y) h ∈ N)
    (hinv : ∀ y, Function.Bijective (quotOp (pullback (P y)) W N (hW y) (hN y)))
    {n : ℕ} (b : Module.Basis (Fin n) ℚ (W ⧸ N.comap W.subtype)) :
    (∀ g ∈ zariskiClosure {g : (Matrix (Fin n) (Fin n) Qbar)ˣ | ∃ y : Y,
          (g : Matrix (Fin n) (Fin n) Qbar) =
            castMat (LinearMap.toMatrix b b (quotOp (pullback (P y)) W N (hW y) (hN y)))},
      ∀ h ∈ zariskiClosure {g : (Matrix (Fin n) (Fin n) Qbar)ˣ | ∃ y : Y,
          (g : Matrix (Fin n) (Fin n) Qbar) =
            castMat (LinearMap.toMatrix b b (quotOp (pullback (P y)) W N (hW y) (hN y)))},
      IsUnipotent (g : Matrix (Fin n) (Fin n) Qbar) → IsUnipotent (h : Matrix (Fin n) (Fin n) Qbar) →
        Commute (g : Matrix (Fin n) (Fin n) Qbar) (h : Matrix (Fin n) (Fin n) Qbar)) ∧
    IsTriangularizableQ (identityComponent (zariskiClosure {g : (Matrix (Fin n) (Fin n) Qbar)ˣ |
      ∃ y : Y, (g : Matrix (Fin n) (Fin n) Qbar) =
        castMat (LinearMap.toMatrix b b (quotOp (pullback (P y)) W N (hW y) (hN y)))})) := by sorry

end CopylessCRA
