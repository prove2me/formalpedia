-- Prove2me | Theorems.Thm_ArbSlowFP_lemma_7_2
-- name    : ArbSlowFP.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:39.745185+00:00
-- url     : https://prove2.me/theorems/14aa2d10-cacb-4231-8a3e-cab217685a58
-- title:
--   Lemma 7.2 — choosing the integer scale factor and correction
-- statement:
--   For the algebraic parent data $(R^\top C,\mathbf 1_m^\top C,\chi,vC=e_{0,k}^\top,c_{\mathrm{ref}})$ there exist an integer scale $\tau\ge1$ and an integer correction row $\ell_*\in\mathbb Z^{1\times w}$ with
--   $$\langle Z^{(h)},(D^\circ)^\top X-\ell_*^\top\psi^\circ\rangle=0\quad\text{for every even }k<h\le2k .$$
--   They can be computed in finitely many steps using exact rational arithmetic. This choice of $(\tau,\ell_*)$ does not depend on row $0$ of $R^\top C$ or on the constant coefficient $\chi_0$.
--
--   **Formalization Note** For fixed data any pair is trivially computable, so the computation clause is stated uniformly: a computable function $F$ takes $k$ and codes of $(R^\top C,\mathbf 1^\top C,\chi,c_{\mathrm{ref}})$ to $\tau$ and codes of $\ell_*$. The conclusion holds for every parent with that data and the identities $AC=RN_k$, $vC=e_{0,k}^\top$, $\chi_{k-1}>0$, and for every baseline $H$. Rationals are coded as $(\mathrm{pos},\mathrm{neg},\mathrm{den})$ for $(\mathrm{pos}-\mathrm{neg})/(\mathrm{den}+1)$, since Mathlib has no `Primcodable` for $\mathbb Z$ or $\mathbb Q$. The independence clause is that $F$ is unchanged when row $0$ of the code of $R^\top C$ and the entry $0$ of the code of $\chi$ change.
--
--   Differences from the source:
--   - reading: "can be computed in finitely many steps" for "the algebraic parent data" → a single Computable F on codes of the data, uniform in k and in the data; reason: for fixed data the clause would say nothing
--   - generalization: the tables in (31) for the parent data listed in the statement, at H = A_k + 3 → for every bare (A, R, C, b, v) on any finite ι : Type with AC = RN_k, vC = e⊤₀, χ_{k−1} > 0 (no skew-symmetry, v_b = 0, rank or trajectory hypothesis), and every H; reason: (41) expresses (D°)⊤X through the listed data using only these identities, H cancels, and p.56 applies the lemma to bare rotated tables; the paper's parents are instances
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.45, Lemma 7.2

import Mathlib
import Definitions.Def_ArbSlowFP_IsAddData

open Matrix

namespace ArbSlowFP

/-- Lemma 7.2, p.45 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). For the algebraic
parent data `(R⊤C, 1⊤C, χ, vC = e⊤₀, cref)` there exist an integer scale `τ ≥ 1` and an integer correction
row `ℓ∗` satisfying (31). They can be computed in finitely many steps using exact rational arithmetic, and
this choice of `(τ, ℓ∗)` does not depend on row 0 of `R⊤C` or on the constant coefficient `χ₀`.

**Formalization Note.** For fixed data any pair is trivially computable, so the clause is stated
uniformly: a computable `F` takes `k` and rational codes of `(R⊤C, 1⊤C, χ, cref)` to `τ` and integer codes
of `ℓ∗`. The conclusion holds for every parent `(A, R, C, b, v)` having that data with the identities
`AC = RN_k`, `vC = e⊤₀`, `χ_{k-1} > 0` and for every `H` (the proof shows (41): `H` and `A` cancel). The
second clause says that `F` is unchanged when row 0 of the code of `R⊤C` and the entry 0 of the code of
`χ` change. No trajectory hypothesis is made (paper p.56). -/
theorem lemma_7_2 :
    ∃ F : ℕ × List (List QCode) × List QCode × List QCode × QCode → ℕ × List (ℕ × ℕ),
      Computable F ∧
      (∀ (k : ℕ) (_hk : 2 ≤ k) (ι : Type) [Fintype ι] [DecidableEq ι] (P : Parent k ι)
          (_hP : P.IsAlgebraic) (cref : ℚ) (_h0 : 0 < cref) (_h1 : cref < 1) (H : ℚ)
          (cRC : List (List QCode)) (cOne cChi : List QCode) (cC : QCode),
        IsMatCode cRC (P.Rᵀ * P.C) → IsRowCode cOne ((1 : ι → ℚ) ᵥ* P.C) →
        IsRowCode cChi (P.R P.b) → decodeQ cC = cref →
        let out := F (k, cRC, cOne, cChi, cC)
        1 ≤ out.1 ∧ out.2.length = k + 1 ∧
        ∀ h, Even h → k < h → h ≤ 2 * k →
          frob (testZ k h)
            (P.testResidual H out.1 cref fun j => decodeZ (out.2.getD (j : ℕ) (0, 0))) = 0) ∧
      ∀ (k : ℕ) (cRC cRC' : List (List QCode)) (cOne cChi cChi' : List QCode) (cC : QCode),
        cRC.tail = cRC'.tail → cChi.tail = cChi'.tail →
          F (k, cRC, cOne, cChi, cC) = F (k, cRC', cOne, cChi', cC) := by sorry

end ArbSlowFP
