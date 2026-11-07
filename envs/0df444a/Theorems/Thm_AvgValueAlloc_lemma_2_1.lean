-- Prove2me | Theorems.Thm_AvgValueAlloc_lemma_2_1
-- name    : AvgValueAlloc.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:06.332411+00:00
-- url     : https://prove2.me/theorems/2da51495-3084-46f7-96b4-e84171cc2971
-- title:
--   Lemma 2.1 — LP geometry
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$, $J$ a set of buyers and $A$ a finite family of records. On banks $B\ge0$:
--
--   1. $F^J_A$ is zero at zero bank, monotone, has bank-coordinate diminishing returns ($F(C+\delta e_j)-F(C)\le F(B+\delta e_j)-F(B)$ for $0\le B\le C$, $\delta\ge0$), and is concave on $\{B\ge0\}$.
--   2. For an added record $u$, the influence $D(B)=F^J_{A+u}(B)-F^J_A(B)$ is nonnegative, coordinatewise nondecreasing, zero at $B=0$, and at most $\max\{u_j: j\in J,\ \rho_j/2\le u_j<\rho_j\}$.
--
--   These properties make $G$ and $G^s$ valid objectives $\hat V$ for the greedy and softmax funding rules and give the bounded record influence used in validation.
--
--   Differences from the source:
--   - encoding: bank-coordinate diminishing returns → F(C + δe_j) − F(C) ≤ F(B + δe_j) − F(B) for 0 ≤ B ≤ C, δ ≥ 0 (IsDRObjective, which also contains monotonicity and F(0) = 0); reason: the standard coordinatewise DR property; same instances
--   - encoding: records A + i → records indexed by Option ι, the new record at none; reason: Lean convention for adding one record; same instances
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.1, Lemma 2.1, p.4

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_edgeLP
import Definitions.Def_AvgValueAlloc_Hobj

namespace AvgValueAlloc

/-- **Lemma 2.1 (LP geometry).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.1, Lemma 2.1, p.4: "F^J_A is monotone, concave, zero at
zero bank and has bank-coordinate diminishing returns. Added-record influence D_i(B) =
F^J_{A+i}(B) − F^J_A(B) is nonnegative, coordinatewise nondecreasing and zero at zero bank. It is
at most that record's maximum retained reward."

For thresholds `ρ > 0`, a buyer set `J` and records `A`, on nonnegative banks:
1. `F^J_A` is zero at zero, monotone, with bank-coordinate diminishing returns
   (`IsDRObjective`), and concave on `{B ≥ 0}`;
2. for any added record `u` (records `A + u`, indexed by `Option ι`), the influence
   `D(B) = F^J_{A+u}(B) − F^J_A(B)` is nonnegative, nondecreasing in `B`, zero at `B = 0`, and at
   most `max {u_j : j ∈ J, ρ_j/2 ≤ u_j < ρ_j}`.

**Formalization Note.** Diminishing returns: `F(C + δe_j) − F(C) ≤ F(B + δe_j) − F(B)` for
`0 ≤ B ≤ C`, `δ ≥ 0`. -/
theorem lemma_2_1 {n : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (J : Finset (Fin n)) {ι : Type}
    [Fintype ι] (A : ι → Vec n) :
    IsDRObjective (Flp ρ J A) ∧ ConcaveOn ℝ {B : Fin n → ℝ | 0 ≤ B} (Flp ρ J A) ∧
      ∀ u : Vec n,
        (∀ B : Fin n → ℝ, 0 ≤ B →
          0 ≤ Flp ρ J (fun o : Option ι => o.elim u A) B - Flp ρ J A B) ∧
        (∀ B C : Fin n → ℝ, 0 ≤ B → B ≤ C →
          Flp ρ J (fun o : Option ι => o.elim u A) B - Flp ρ J A B ≤
            Flp ρ J (fun o : Option ι => o.elim u A) C - Flp ρ J A C) ∧
        Flp ρ J (fun o : Option ι => o.elim u A) 0 - Flp ρ J A 0 = 0 ∧
        (∀ B : Fin n → ℝ, 0 ≤ B →
          Flp ρ J (fun o : Option ι => o.elim u A) B - Flp ρ J A B ≤ maxRetained ρ J u) := by sorry

end AvgValueAlloc
