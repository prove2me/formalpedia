-- Prove2me | Theorems.Thm_CompNonlocal_Supplement_theorem_10_werner_certification_implies_dowpuzz
-- name    : CompNonlocal.Supplement.theorem_10_werner_certification_implies_dowpuzz
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:14:52.293692+00:00
-- url     : https://prove2.me/theorems/8827e90b-69d1-4e2b-8aa1-9afdc7c3f0a7
-- title:
--   Theorem 10 — public-verification certification of $\rho(v)$ above $\Gamma_{\mathrm{stat}}(v)$ implies a distributional one-way puzzle
-- statement:
--   Fix $v\in(1/3,1]$. Suppose $\rho(v)$ has a one-round, single-copy certificate with public verification (the verifier retains no private register), uniform quantum polynomial-time $Q,A,B,\mathrm{Val}$, completeness $c$ and soundness $s$ against polynomial-size players with advice on separable two-qubit states. If for some inverse-polynomial $g>0$ and all sufficiently large $\kappa$
--   $$c(\kappa)-s(\kappa)\ \ge\ \Gamma_{\mathrm{stat}}(v)+g(\kappa),\qquad \Gamma_{\mathrm{stat}}(v)=\tfrac12\big(v-\tfrac12\big)_+,$$
--   then $(\mathrm{puzz},\mathrm{ans}):=(X,Y)\leftarrow Q(1^\kappa)$ is a distributional one-way puzzle (Definition 7).
--
--   In particular, for $v\le1/2$ any inverse-polynomial gap suffices.
--
--   Differences from the source:
--   - encoding: inverse-polynomial g = g(κ) > 0 → g > 0 with g(κ) ≥ 1/(q(κ)+1) for all sufficiently large κ, for a polynomial q; reason: any such g can be replaced by 1/(q(κ)+1), which is inverse-polynomial and still satisfies the gap condition; same theorem
--   - reading: one-round, single-copy public-verification certificate with gap γ = c − s → the published Certificate with uniform Q, A, B, Val, (Q κ).outQ = [] for every κ, and the completeness and soundness clauses of the published IsCertificateFor for ρ(v) with functions c, s : ℕ → [0, 1]; reason: public verification means Val reads no retained register; the clause γ > 1/poly of Definition 10 follows from the gap hypothesis and is not assumed separately
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Theorem 10, p.66 (proof Appendix E, p.84)

import Mathlib
import Definitions.Def_CompNonlocal_Certificate_acc
import Definitions.Def_CompNonlocal_Uniform
import Definitions.Def_CompNonlocal_werner
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_CompNonlocal_Supplement_gammaStat
import Definitions.Def_CompNonlocal_Supplement_IsDOWPuzz

set_option autoImplicit false

namespace CompNonlocal.Supplement

open CompNonlocal

/-- Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Theorem 10, p.66 (proof in Appendix E, p.84): "Theorem 10 (Werner certification above the
statistical bound implies OWPuzz). Fix v ∈ (1/3, 1]. Suppose ρ(v) has a one-round, single-copy
public-verification certificate with gap γ = c − s. If, for some inverse-polynomial g = g(κ) > 0
and all sufficiently large κ, γ ≥ Γstat(v) + g, Γstat(v) := (1/2)(v − 1/2)_+, then (puzz, ans) :=
(X, Y) ← Q(1^κ) is a distributional one-way puzzle."

Hypotheses: `c` is a one-round single-copy certificate (the published `Certificate`, Definitions
9–11 with `k = 1`; acceptance is Val's first output bit, i.e. `v₁ < 0`) with uniform QPT `Q`, `A`,
`B`, `Val`; public verification: `Q` retains no register (`outQ = []` at every `κ`); completeness
`cc` on `ρ(v)` for all sufficiently large `κ`; soundness `s` against every pair of polynomial-size
players with advice and every family of separable two-qubit states, eventually (onset depending on
the strategy) — exactly the clauses of the published `IsCertificateFor`; and `cc − s ≥ Γstat(v) + g`
eventually, with `g > 0` and `g ≥ 1/(q + 1)` eventually for a polynomial `q`. Conclusion: `Q` itself,
with `puzz = x` (the first `lx κ` bits of its output) and `ans = y` (the rest), is a dOWPuzz
(Definition 7). -/
theorem theorem_10_werner_certification_implies_dowpuzz (v : ℝ) (hv₁ : 1 / 3 < v) (hv₂ : v ≤ 1)
    (c : Certificate) (hQ : Uniform c.Qg) (hA : Uniform c.A) (hB : Uniform c.B)
    (hV : Uniform c.Val) (hpub : ∀ κ : ℕ, (c.Qg κ).outQ = [])
    (cc s : ℕ → ℝ) (hcc : ∀ κ, 0 ≤ cc κ ∧ cc κ ≤ 1) (hs : ∀ κ, 0 ≤ s κ ∧ s κ ≤ 1)
    (hcomp : ∀ᶠ κ in Filter.atTop, cc κ ≤ c.acc κ c.A c.B (werner v))
    (hsound : ∀ A' B' : Family, PolySize A' → PolySize B' →
      ∀ τ : ℕ → Matrix (Bool × Bool) (Bool × Bool) ℂ,
        (∀ κ, QAlgorithms.Entanglement.IsSeparableDensity (τ κ)) →
        ∀ᶠ κ in Filter.atTop, c.acc κ A' B' (τ κ) ≤ s κ)
    (g : ℕ → ℝ) (hg : ∀ κ, 0 < g κ)
    (hginv : ∃ q : Polynomial ℕ, ∀ᶠ κ in Filter.atTop, 1 / ((q.eval κ : ℕ) + 1 : ℝ) ≤ g κ)
    (hgap : ∀ᶠ κ in Filter.atTop, gammaStat v + g κ ≤ cc κ - s κ) :
    IsDOWPuzz c.Qg c.lx := by sorry

end CompNonlocal.Supplement
