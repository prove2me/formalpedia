-- Prove2me | Theorems.Thm_Erdos287_no_endpoint_extremal_pair_cover_above_shared_square_endpoint
-- name    : Erdos287.no_endpoint_extremal_pair_cover_above_shared_square_endpoint
-- status  : Open
-- author  : @immiq
-- created : 2026-11-27T00:26:42.079609+00:00
-- url     : https://prove2.me/theorems/0a9fcd3c-b608-47af-a648-1ca6788ac3a2
-- title:
--   No endpoint-extremal exact pair cover beyond the checked interval
-- statement:
--   Exclude exact adjacent-pair covers beyond the proven cutoff. The cover may be assumed to first minimize its largest denominator, then maximize its smallest denominator, then minimize cardinality. It satisfies the proven obstruction to trimming either endpoint and the divisor-indexed split bounds.
-- source:
--   Erdős Problem 287, remaining range after the checked finite certificate

import Mathlib
open Finset

theorem Erdos287.no_endpoint_extremal_pair_cover_above_shared_square_endpoint
    (D : Finset ℕ) (m M : ℕ) (hm : 1 < m) (hlarge : 18307388200484069835662842214588395405985911084266618419177128943728800151883004813411682115562538821989695191559043444776223454183935370598472648044059494865423977378654321965570698155279201499564906496821342366449211724496667295157056764999308951244675322774053170315388966514907635514521215935252367692727200372092044296669494840919129095723500197461655677595190886809949658465523639224979402079202752948961490050797817396873111763511976797326829608422278005317935343399025590155638682696407774223468117287656398109685745954312337961184942712922701700028904920185300241885928365796600693646138399642211309461859391441032375802439590158184713609039573799720909309874719322553089648099234725873944118762781478245620609813123387294227899694730801194030144533833449551459854448687956102625394224545555454456033103369508603015889877979318232648868568711031487140528881403300064019065023714949735704308329870042620071585098369700197136345107305368548983782271863451669234052 < M)
    (hmD : m ∈ D) (hMD : M ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hextreme : ∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) →
      M ≤ b ∧ (b = M → a ≤ m) ∧ (b = M → a = m → D.card ≤ F.card))
    (htrim : ∀ (A : Finset ℕ) (l u : ℕ), m ≤ l → u ≤ M → m < l ∨ u < M →
      A ⊆ Finset.Icc l u → Disjoint A D →
      (∑ n ∈ A, (1 : ℚ) / n) ≠
        ∑ n ∈ D.filter (fun n => n < l ∨ u < n), (1 : ℚ) / n)
    (hsplits : ∀ B : Finset ℕ,
      (∀ d ∈ B, 0 < d ∧ d < m ∧ d ∣ m * m ∧ m + m * m / d ≤ M) →
      let S := D.filter (fun n => ∃ d ∈ B, n = m + d ∨ n = m + m * m / d)
      B.card ≤ S.card ∧
        (∑ d ∈ B, (1 : ℚ) / ((m + m * m / d : ℕ) : ℚ)) ≤ ∑ n ∈ S, (1 : ℚ) / n) :
    False := by sorry
