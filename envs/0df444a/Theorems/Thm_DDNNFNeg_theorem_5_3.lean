-- Prove2me | Theorems.Thm_DDNNFNeg_theorem_5_3
-- name    : DDNNFNeg.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:59.516695+00:00
-- url     : https://prove2.me/theorems/9e5c3e03-5e61-4a48-b37d-961c20b6eea0
-- title:
--   Theorem 5.3 — $\mathrm{Cov}^m_0(f_G) = 2^{\Theta(n)}$, so the smallest DNNF computing $\neg f_G$ has $2^{\Theta(n)}$ gates
-- statement:
--   Let $\gamma \in (0,1)$. There are $\kappa, K > 0$ and $n_0$, depending only on $\gamma$, such that for every $n \ge n_0$ and every simple 3-regular balanced-cut $\gamma$-edge expander $G$ on $[n]$ with a proper 3-edge-colouring:
--
--   1. $2^{\kappa n} \le \mathrm{Cov}^m_0(f_G) \le 2^{K n}$;
--   2. every DNNF computing $\neg f_G$ has at least $2^{\kappa n}$ gates;
--   3. some DNNF computing $\neg f_G$ has at most $2^{K n}$ gates.
--
--   In the paper's words: $\mathrm{Cov}^m_0(f_G) = 2^{\Theta(n)}$, and therefore the smallest DNNF computing $\neg f_G$ has $2^{\Theta(n)}$ gates. This is the lower half of the separation in Theorem 1.1.
--
--   **Formalization Note** The circuits in clause 2 may use constant leaves; the circuit in clause 3 is constant-free.
--
--   Differences from the source:
--   - generalization: G as promised by Proposition 5.2, with its fixed γ → every γ ∈ (0,1), with constants depending only on γ; reason: the paper's γ is one instance
--   - generalization: the smallest DNNF (literal input gates only) computing ¬f_G has ≥ 2^{Ω(n)} gates → every DNNF computing ¬f_G, constant leaves allowed, has ≥ 2^{κn} gates; reason: a larger class; every constant-free DNNF is one
--   - reading: 2^{Θ(n)} → 2^{κn} ≤ · ≤ 2^{Kn} for all n ≥ n₀, with κ, K > 0 and n₀ depending only on γ; reason: the standard reading of Θ
--   - encoding: the size of the smallest DNNF → a universal lower-bound clause and an existential (constant-free) upper-bound clause; reason: equivalent formulation of a minimum
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Theorem 5.3, p.12 (proof p.15)

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_Computes
import Definitions.Def_DDNNFNeg_NNF_IsConstFree
import Definitions.Def_DDNNFNeg_NNF_IsDNNF
import Definitions.Def_DDNNFNeg_coverNumberMulti
import Definitions.Def_DDNNFNeg_fG
import Definitions.Def_DDNNFNeg_IsBalancedCutExpander
import Definitions.Def_DDNNFNeg_IsProperEdgeColoring

namespace DDNNFNeg

/-- **Theorem 5.3** (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.12): `Cov^m_0(f_G) = 2^{Θ(n)}`; therefore the smallest DNNF computing
`¬f_G` has `2^{Θ(n)}` gates.

**Formalization Note** The setting is that of §5.2 (`G` a simple 3-regular balanced-cut
`γ`-edge expander on `Fin n` with a proper 3-edge-colouring), for every `γ ∈ (0, 1)` rather
than the one `γ` of Proposition 5.2. `2^{Θ(n)}` is read as two bounds `2^{κn} ≤ · ≤ 2^{Kn}`
for `n ≥ n₀`, with `κ, K > 0` and `n₀` depending only on `γ`. The minimum DNNF size is made
explicit: every DNNF computing `¬f_G`, even one with constant leaves (a larger class than the
paper's), has at least `2^{κn}` gates, and some constant-free DNNF computing `¬f_G` has at most
`2^{Kn}` gates. -/
theorem theorem_5_3 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ κ K : ℝ, 0 < κ ∧ 0 < K ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.IsRegularOfDegree 3 →
      IsBalancedCutExpander γ G → ∀ c : Sym2 (Fin n) → Fin 3, IsProperEdgeColoring G c →
      (2 : ℝ) ^ (κ * n) ≤ (coverNumberMulti false (fG G c) : ℝ) ∧
      (coverNumberMulti false (fG G c) : ℝ) ≤ (2 : ℝ) ^ (K * n) ∧
      (∀ D : NNF (Fin n), D.IsDNNF → D.Computes (fun x => !fG G c x) →
        (2 : ℝ) ^ (κ * n) ≤ (D.size : ℝ)) ∧
      (∃ D : NNF (Fin n), D.IsConstFree ∧ D.IsDNNF ∧ D.Computes (fun x => !fG G c x) ∧
        (D.size : ℝ) ≤ (2 : ℝ) ^ (K * n)) := by sorry

end DDNNFNeg
