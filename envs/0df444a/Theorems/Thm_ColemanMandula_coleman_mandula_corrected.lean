-- Prove2me | Theorems.Thm_ColemanMandula_coleman_mandula_corrected
-- name    : ColemanMandula.coleman_mandula_corrected
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-24T05:06:33.088527+00:00
-- url     : https://prove2.me/theorems/5b1e3b40-b7f9-4acf-8ef0-986a64c8b007
-- title:
--   Coleman–Mandula theorem (infinitesimal form, Lemma 9; massive particles)
-- statement:
--   **Coleman–Mandula theorem, infinitesimal form (Lemma 9).** Let $D$ be Lorentz-invariant scattering data satisfying particle finiteness, weak elastic analyticity and occurrence of scattering, in which **every particle has positive mass**. Let $\mathfrak A$ be a set of operators on one-particle momentum-space wave functions such that
--
--   - every $A\in\mathfrak A$ is Hermitian and acts on the mass hyperboloids as a differential operator in the momentum with smooth matrix coefficients, of a finite order $N_A$ that is **the same on every hyperboloid** (the form of the generators given by Lemmas 1–2 under assumption 5, with the single order $N$ used in the proof of Lemma 9);
--   - $\mathfrak A$ is closed under sums and real multiples, contains the translation generators $P_a$ (multiplication by $a\cdot p$) and the Lorentz generators $M_X$, $X\in\mathfrak{so}(3,1)$, and is closed under $A\mapsto i[P_a,A]$;
--   - every $A\in\mathfrak A$ that commutes with all translations is (on test functions) a multiplication operator $B\in\mathfrak B_S$ — a smooth, Hermitian multiplier whose two-particle action commutes with the $S$ matrix.
--
--   Then every $A\in\mathfrak A$ is, on test functions, the sum of an infinitesimal Lorentz transformation, an infinitesimal translation and an infinitesimal internal symmetry transformation:
--   $$A=M_X+a\cdot P+b,\qquad X\in\mathfrak{so}(3,1),\ a\in\mathbb R^4,\ b \text{ internal}.$$
--
--   *Revision note.* Without the positive-mass hypothesis the statement is false (a massless scalar with the dilation generator $i(v\cdot\nabla_v+1)$ is a counterexample, formally checked by the drafter); see the correction note in the mission description.
-- source:
--   S. Coleman and J. Mandula, All Possible Symmetries of the S Matrix, Phys. Rev. 159 (1967) 1251-1256, https://doi.org/10.1103/PhysRev.159.1251, p. 1252 (Theorem, Sec. I.A) and p. 1256, Lemma 9 (Eqs. (31)–(36))

import Definitions.Def_ColemanMandula_Scattering

open Matrix
open scoped Kronecker ContDiff

namespace ColemanMandula

/-- **Candidate corrected goal (unproved).** This is the original statement with two changes:
* `hmassive`: every particle has positive mass. This excludes the massless counterexample
  (a single massless scalar with the dilation generator), formally checked in
  `Statements/GoalCounterexample.lean` of the drafting project.
* `h_diff` is `ScatteringData.IsLocalDiffOp` with one bound `n` on the order of each generator
  that holds on all hyperboloids (instead of a bound `N k` depending on the shell `k`). This matches the paper's use of a single finite order `N`
  in the proof of Lemma 9. We have not shown that this second change is necessary.

This statement has not been proved or disproved. -/
theorem coleman_mandula_corrected (D : ScatteringData)
    (hfin : D.ParticleFinite) (hana : D.ElasticAnalytic) (hscat : D.ScatteringOccurs)
    (hmassive : ∀ k, 0 < D.mass k)
    (𝔄 : Set D.Op)
    (h_diff : ∀ A ∈ 𝔄, ∃ n : ℕ,
      ∃ C : (k : D.Shell) → (j : ℕ) → (Fin j → Fin 3) → ThreeVec →
          Matrix (Fin (D.mult k)) (Fin (D.mult k)) ℂ,
        (∀ k j α, ContDiffOn ℝ ∞
            (fun v => Matrix.of.symm (C k j α v))
            (shellDomain (D.mass k))) ∧
        ∀ f, D.IsTestFn f → ∀ k, ∀ v ∈ shellDomain (D.mass k),
          A f k v = ∑ j ∈ Finset.range (n + 1), ∑ α : Fin j → Fin 3,
            C k j α v *ᵥ
              (iteratedFDeriv ℝ j (f k) v (fun i => EuclideanSpace.single (α i) (1 : ℝ))))
    (h_herm : ∀ A ∈ 𝔄, D.IsHermitianOp A)
    (h_add : ∀ A ∈ 𝔄, ∀ A' ∈ 𝔄, A + A' ∈ 𝔄)
    (h_smul : ∀ r : ℝ, ∀ A ∈ 𝔄, (r : ℂ) • A ∈ 𝔄)
    (h_trans : ∀ a : FourVec, ∀ A ∈ 𝔄, Complex.I • D.comm (D.momOp a) A ∈ 𝔄)
    (h_mom : ∀ a : FourVec, D.momOp a ∈ 𝔄)
    (h_lor : ∀ X, IsLorentzGen X → D.lorentzGen X ∈ 𝔄)
    (h_symm : ∀ A ∈ 𝔄,
      (∀ a : FourVec, ∀ f, D.IsTestFn f → A (D.momOp a f) = D.momOp a (A f)) →
      ∃ B : D.Multiplier, D.IsSymMultiplier B ∧
        ∀ f, D.IsTestFn f → ∀ k, ∀ v ∈ shellDomain (D.mass k), A f k v = D.multOp B f k v) :
    ∀ A ∈ 𝔄, ∃ X, IsLorentzGen X ∧ ∃ (a : FourVec) (b : D.Multiplier), D.IsInternal b ∧
      ∀ f, D.IsTestFn f → ∀ k, ∀ v ∈ shellDomain (D.mass k),
        A f k v = D.lorentzGen X f k v + D.momOp a f k v + D.multOp b f k v := by
  sorry

end ColemanMandula
