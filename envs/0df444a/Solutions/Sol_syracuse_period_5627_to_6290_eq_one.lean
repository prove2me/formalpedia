-- Prove2me | solution 1 for syracuse_period_5627_to_6290_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T09:04:05.244032+00:00
-- url     : https://prove2.me/submissions/3ecbbe75-adba-4450-ac04-87fec277db4a

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_cycle_eq_one_of_margin_at
import Theorems.Thm_syracuse_no_cycle_below_1883432

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

/-
DRAFT ASSEMBLY ONLY: this new file has not been compiled or machine-verified.

Public mission dependencies, both Proved/public in the refreshed metadata:
* syracuse_cycle_eq_one_of_margin_at:
  756c30cf-ce03-4b10-afe8-8f76f671ae4f.
* syracuse_no_cycle_below_1883432:
  33c2cf17-1597-4cb1-b85c-28dd910af0c9.
Environment: Lean v4.33.1 and Mathlib
0df444a360eaa60ab8c11dca51a86af692955474.

Only local supporting source retained:
prove2me_workspace/Solutions/Sol_collatz_cycle_margin_5627_6290.lean,
lines 11-143: repeated squaring, the 664-entry exponent table, its closed
kernel decision, and the arbitrary-K finite arithmetic margin theorem.
No local cycle criterion/tools, Solutions import, additional finite trajectory
band, target import, admission, custom axiom, or native_decide is included.
This result excludes all return periods 5627-6290; period 5626 and the
unbounded tail from 6291 are explicitly outside its scope.
-/

namespace CollatzCycleIntervalDraft5627To6290V02

-- Structurally recursive repeated squaring; all evaluations below are checked
-- by the kernel. The correctness theorem connects it to ordinary Nat powers.
def binaryPow : Nat → Nat → Nat → Nat
  | _, _, 0 => 1
  | a, n, fuel + 1 =>
      let r := binaryPow a (n / 2) fuel
      if n % 2 = 0 then r * r else r * r * a

theorem binaryPow_eq (a n fuel : Nat) (h : n < 2 ^ fuel) :
    binaryPow a n fuel = a ^ n := by
  induction fuel generalizing n with
  | zero =>
      have hn : n = 0 := by simpa using h
      subst n
      rfl
  | succ fuel ih =>
      have hn : n / 2 < 2 ^ fuel := by
        rw [pow_succ] at h
        omega
      simp only [binaryPow, ih (n / 2) hn]
      split
      · rename_i heven
        have he : n = n / 2 + n / 2 := by omega
        rw [← pow_add, ← he]
      · rename_i hodd
        have he : n = n / 2 + n / 2 + 1 := by omega
        rw [← pow_add, ← pow_succ, ← he]

-- Entry i was generated as bit_length(3^(5627+i)). No external arithmetic
-- result is trusted: the lower bounds and margins are certified below.
def exponentTable : List Nat :=
  [8919, 8921, 8922, 8924, 8925, 8927, 8929, 8930, 8932, 8933, 8935, 8937,
   8938, 8940, 8941, 8943, 8944, 8946, 8948, 8949, 8951, 8952, 8954, 8956,
   8957, 8959, 8960, 8962, 8963, 8965, 8967, 8968, 8970, 8971, 8973, 8975,
   8976, 8978, 8979, 8981, 8982, 8984, 8986, 8987, 8989, 8990, 8992, 8994,
   8995, 8997, 8998, 9000, 9002, 9003, 9005, 9006, 9008, 9009, 9011, 9013,
   9014, 9016, 9017, 9019, 9021, 9022, 9024, 9025, 9027, 9028, 9030, 9032,
   9033, 9035, 9036, 9038, 9040, 9041, 9043, 9044, 9046, 9047, 9049, 9051,
   9052, 9054, 9055, 9057, 9059, 9060, 9062, 9063, 9065, 9066, 9068, 9070,
   9071, 9073, 9074, 9076, 9078, 9079, 9081, 9082, 9084, 9086, 9087, 9089,
   9090, 9092, 9093, 9095, 9097, 9098, 9100, 9101, 9103, 9105, 9106, 9108,
   9109, 9111, 9112, 9114, 9116, 9117, 9119, 9120, 9122, 9124, 9125, 9127,
   9128, 9130, 9131, 9133, 9135, 9136, 9138, 9139, 9141, 9143, 9144, 9146,
   9147, 9149, 9150, 9152, 9154, 9155, 9157, 9158, 9160, 9162, 9163, 9165,
   9166, 9168, 9170, 9171, 9173, 9174, 9176, 9177, 9179, 9181, 9182, 9184,
   9185, 9187, 9189, 9190, 9192, 9193, 9195, 9196, 9198, 9200, 9201, 9203,
   9204, 9206, 9208, 9209, 9211, 9212, 9214, 9215, 9217, 9219, 9220, 9222,
   9223, 9225, 9227, 9228, 9230, 9231, 9233, 9234, 9236, 9238, 9239, 9241,
   9242, 9244, 9246, 9247, 9249, 9250, 9252, 9254, 9255, 9257, 9258, 9260,
   9261, 9263, 9265, 9266, 9268, 9269, 9271, 9273, 9274, 9276, 9277, 9279,
   9280, 9282, 9284, 9285, 9287, 9288, 9290, 9292, 9293, 9295, 9296, 9298,
   9299, 9301, 9303, 9304, 9306, 9307, 9309, 9311, 9312, 9314, 9315, 9317,
   9318, 9320, 9322, 9323, 9325, 9326, 9328, 9330, 9331, 9333, 9334, 9336,
   9338, 9339, 9341, 9342, 9344, 9345, 9347, 9349, 9350, 9352, 9353, 9355,
   9357, 9358, 9360, 9361, 9363, 9364, 9366, 9368, 9369, 9371, 9372, 9374,
   9376, 9377, 9379, 9380, 9382, 9383, 9385, 9387, 9388, 9390, 9391, 9393,
   9395, 9396, 9398, 9399, 9401, 9402, 9404, 9406, 9407, 9409, 9410, 9412,
   9414, 9415, 9417, 9418, 9420, 9422, 9423, 9425, 9426, 9428, 9429, 9431,
   9433, 9434, 9436, 9437, 9439, 9441, 9442, 9444, 9445, 9447, 9448, 9450,
   9452, 9453, 9455, 9456, 9458, 9460, 9461, 9463, 9464, 9466, 9467, 9469,
   9471, 9472, 9474, 9475, 9477, 9479, 9480, 9482, 9483, 9485, 9487, 9488,
   9490, 9491, 9493, 9494, 9496, 9498, 9499, 9501, 9502, 9504, 9506, 9507,
   9509, 9510, 9512, 9513, 9515, 9517, 9518, 9520, 9521, 9523, 9525, 9526,
   9528, 9529, 9531, 9532, 9534, 9536, 9537, 9539, 9540, 9542, 9544, 9545,
   9547, 9548, 9550, 9551, 9553, 9555, 9556, 9558, 9559, 9561, 9563, 9564,
   9566, 9567, 9569, 9571, 9572, 9574, 9575, 9577, 9578, 9580, 9582, 9583,
   9585, 9586, 9588, 9590, 9591, 9593, 9594, 9596, 9597, 9599, 9601, 9602,
   9604, 9605, 9607, 9609, 9610, 9612, 9613, 9615, 9616, 9618, 9620, 9621,
   9623, 9624, 9626, 9628, 9629, 9631, 9632, 9634, 9635, 9637, 9639, 9640,
   9642, 9643, 9645, 9647, 9648, 9650, 9651, 9653, 9655, 9656, 9658, 9659,
   9661, 9662, 9664, 9666, 9667, 9669, 9670, 9672, 9674, 9675, 9677, 9678,
   9680, 9681, 9683, 9685, 9686, 9688, 9689, 9691, 9693, 9694, 9696, 9697,
   9699, 9700, 9702, 9704, 9705, 9707, 9708, 9710, 9712, 9713, 9715, 9716,
   9718, 9719, 9721, 9723, 9724, 9726, 9727, 9729, 9731, 9732, 9734, 9735,
   9737, 9739, 9740, 9742, 9743, 9745, 9746, 9748, 9750, 9751, 9753, 9754,
   9756, 9758, 9759, 9761, 9762, 9764, 9765, 9767, 9769, 9770, 9772, 9773,
   9775, 9777, 9778, 9780, 9781, 9783, 9784, 9786, 9788, 9789, 9791, 9792,
   9794, 9796, 9797, 9799, 9800, 9802, 9803, 9805, 9807, 9808, 9810, 9811,
   9813, 9815, 9816, 9818, 9819, 9821, 9823, 9824, 9826, 9827, 9829, 9830,
   9832, 9834, 9835, 9837, 9838, 9840, 9842, 9843, 9845, 9846, 9848, 9849,
   9851, 9853, 9854, 9856, 9857, 9859, 9861, 9862, 9864, 9865, 9867, 9868,
   9870, 9872, 9873, 9875, 9876, 9878, 9880, 9881, 9883, 9884, 9886, 9887,
   9889, 9891, 9892, 9894, 9895, 9897, 9899, 9900, 9902, 9903, 9905, 9907,
   9908, 9910, 9911, 9913, 9914, 9916, 9918, 9919, 9921, 9922, 9924, 9926,
   9927, 9929, 9930, 9932, 9933, 9935, 9937, 9938, 9940, 9941, 9943, 9945,
   9946, 9948, 9949, 9951, 9952, 9954, 9956, 9957, 9959, 9960, 9962, 9964,
   9965, 9967, 9968, 9970]

def firstK (p : Nat) : Nat := exponentTable.getD (p - 5627) 0

-- This closed decision covers exactly 664 periods. Fuel 14 is sufficient
-- because both the periods and the tabulated exponents are below 2^14.
theorem finite_period_certificate :
    ∀ i : Fin 664,
      0 < firstK (5627 + i.val) ∧ firstK (5627 + i.val) < 16384 ∧
      binaryPow 2 (firstK (5627 + i.val) - 1) 14 ≤ binaryPow 3 (5627 + i.val) 14 ∧
      binaryPow (3 * 1883432 + 1) (5627 + i.val) 14 <
        binaryPow 2 (firstK (5627 + i.val)) 14 * binaryPow 1883432 (5627 + i.val) 14 := by
  decide +kernel

theorem finite_period_margins (p : Nat) (hp : 5627 ≤ p) (hp' : p ≤ 6290) :
    0 < firstK p ∧ (2 : Nat) ^ (firstK p - 1) ≤ 3 ^ p ∧
      (3 * 1883432 + 1 : Nat) ^ p < 2 ^ firstK p * 1883432 ^ p := by
  let i : Fin 664 := ⟨p - 5627, by omega⟩
  have hpi : 5627 + i.val = p := by dsimp [i]; omega
  have hc := finite_period_certificate i
  rw [hpi] at hc
  have hsP : p < 2 ^ 14 := by change p < 16384; omega
  have hsK : firstK p < 2 ^ 14 := hc.2.1
  have hsKm : firstK p - 1 < 2 ^ 14 :=
    lt_of_le_of_lt (Nat.sub_le _ _) hsK
  have hlow : (2 : Nat) ^ (firstK p - 1) ≤ 3 ^ p := by
    simpa only [binaryPow_eq 2 (firstK p - 1) 14 hsKm,
      binaryPow_eq 3 p 14 hsP] using hc.2.2.1
  have hmargin : (3 * 1883432 + 1 : Nat) ^ p < 2 ^ firstK p * 1883432 ^ p := by
    simpa only [binaryPow_eq (3 * 1883432 + 1) p 14 hsP,
      binaryPow_eq 2 (firstK p) 14 hsK, binaryPow_eq 1883432 p 14 hsP] using hc.2.2.2
  exact ⟨hc.1, hlow, hmargin⟩

-- The exact finite arithmetic extension: arbitrary K, not just table entries.
theorem margin_5627_6290 (p K : Nat) (hp : 5627 ≤ p) (hp' : p ≤ 6290)
    (h3 : (3 : Nat) ^ p < 2 ^ K) :
    (3 * 1883432 + 1 : Nat) ^ p < 2 ^ K * 1883432 ^ p := by
  have hc := finite_period_margins p hp hp'
  have hK : firstK p ≤ K := by
    by_cases h : firstK p ≤ K
    · exact h
    · have hle : K ≤ firstK p - 1 := by have hpos := hc.1; omega
      have hpow : (2 : Nat) ^ K ≤ 2 ^ (firstK p - 1) :=
        Nat.pow_le_pow_right (by decide) hle
      exact False.elim ((Nat.not_lt_of_ge (hpow.trans hc.2.1)) h3)
  exact hc.2.2.trans_le (Nat.mul_le_mul_right (1883432 ^ p)
    (Nat.pow_le_pow_right (by decide) hK))

end CollatzCycleIntervalDraft5627To6290V02

-- Stronger than a minimal-period result: every positive periodic point with
-- any return time in this finite interval is one.
theorem solution :
    ∀ m p : ℕ, 0 < m → 5627 ≤ p → p ≤ 6290 →
      syracuseStep^[p] m = m → m = 1 := by
  intro m p hm hp hp' hcycle
  exact syracuse_cycle_eq_one_of_margin_at
    p m 1883432 (by omega) hm (by decide) hcycle
    (by
      intro z b hz hb hbound hcyc
      exact syracuse_no_cycle_below_1883432 z b hz hb (by omega) hcyc)
    (fun K h3 =>
      CollatzCycleIntervalDraft5627To6290V02.margin_5627_6290
        p K hp hp' h3)

#print axioms solution
