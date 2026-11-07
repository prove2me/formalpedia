-- Prove2me | Theorems.Thm_DDNNFNeg_proposition_5_1
-- name    : DDNNFNeg.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:24:22.19731+00:00
-- url     : https://prove2.me/theorems/a2ac9271-7477-4695-935f-ca07954b7746
-- title:
--   Proposition 5.1 — the d-DNNF size of $f_G$ is $\Theta(n)$
-- statement:
--   There are constants $c_1, C_1 > 0$ and $n_0$ such that for every $n \ge n_0$, every 3-regular graph $G$ on $[n]$ and every proper 3-edge-colouring of $G$:
--
--   1. some constant-free d-DNNF of size at most $C_1 n$ computes $f_G$;
--   2. every d-DNNF computing $f_G$ has size at least $c_1 n$.
--
--   Together: the d-DNNF size of $f_G$ is $\Theta(n)$. This is the upper half of the separation in Theorem 1.1.
--
--   **Formalization Note** The d-DNNF size (a minimum) is written as the pair "some circuit of size $\le C_1 n$" / "every circuit has size $\ge c_1 n$".
--
--   Differences from the source:
--   - reading: Θ(n) → ∃ c₁, C₁ > 0 and n₀ such that for all n ≥ n₀ both bounds hold; reason: the standard reading of Θ with absolute constants
--   - generalization: the lower bound for the d-DNNF size (constant-free d-DNNFs) → every d-DNNF computing f_G, constant leaves allowed, has size ≥ c₁n; reason: a larger class; every constant-free d-DNNF is one, so it specializes to the paper's lower bound
--   - encoding: the d-DNNF size of f_G (least size) → an existence clause for the upper bound and a universal clause for the lower bound; reason: equivalent formulation of a minimum
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Proposition 5.1, p.11 (proof pp.11–12)

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_Computes
import Definitions.Def_DDNNFNeg_NNF_IsConstFree
import Definitions.Def_DDNNFNeg_NNF_IsDDNNF
import Definitions.Def_DDNNFNeg_fG
import Definitions.Def_DDNNFNeg_IsProperEdgeColoring

namespace DDNNFNeg

/-- **Proposition 5.1** (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.11): the d-DNNF size of `f_G` is `Θ(n)`, for every 3-regular
graph `G` on `[n]` with a proper 3-edge-colouring `c`. Both halves: some constant-free d-DNNF
of size `≤ C₁ n` computes `f_G`, and every d-DNNF computing `f_G` has size `≥ c₁ n`.

**Formalization Note** `Θ(n)` is read with absolute constants `c₁, C₁ > 0` and a threshold
`n₀`. The upper half is over the paper's class (`IsConstFree ∧ IsDDNNF`); the lower half
quantifies over d-DNNFs that may also use constant leaves, a larger class, so it specializes to
the paper's d-DNNF size. -/
theorem proposition_5_1 :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.IsRegularOfDegree 3 →
      ∀ c : Sym2 (Fin n) → Fin 3, IsProperEdgeColoring G c →
      (∃ D : NNF (Fin n), D.IsConstFree ∧ D.IsDDNNF ∧ D.Computes (fG G c) ∧
          (D.size : ℝ) ≤ C₁ * n) ∧
      (∀ D : NNF (Fin n), D.IsDDNNF → D.Computes (fG G c) → c₁ * n ≤ (D.size : ℝ)) := by sorry

end DDNNFNeg
